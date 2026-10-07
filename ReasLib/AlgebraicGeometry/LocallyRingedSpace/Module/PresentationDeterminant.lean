module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Invertible
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Epi
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Invertible.Duality
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Determinant maps of finite locally free presentations

This file constructs the determinant map of a short exact presentation by finite locally free
modules. The source is defined for every virtual rank, using the zero object when the virtual
rank is negative.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry SheafOfModules
open scoped AlgebraicGeometry ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant

variable {X : LocallyRingedSpace.{u}} {S : ShortComplex X.Modules}

/-- The source of the determinant map of a presentation: the exterior power in nonnegative
virtual rank and the zero object in negative virtual rank. -/
noncomputable def presentationSource (S : ShortComplex X.Modules) (r₁ r₀ : ℕ) : X.Modules :=
  if r₁ ≤ r₀ then Λ[r₀ - r₁] S.X₃ else 0

/-- In nonnegative virtual rank, the presentation source is canonically the corresponding
exterior power of the presented module. -/
noncomputable def presentationSourceIsoOfLE (S : ShortComplex X.Modules)
    (r₁ r₀ : ℕ) (h : r₁ ≤ r₀) :
    presentationSource S r₁ r₀ ≅ Λ[r₀ - r₁] S.X₃ :=
  eqToIso (by simp [presentationSource, h])

/-- In negative virtual rank, the presentation source is canonically the zero object. -/
noncomputable def presentationSourceIsoZeroOfLT (S : ShortComplex X.Modules)
    (r₁ r₀ : ℕ) (h : r₀ < r₁) :
    presentationSource S r₁ r₀ ≅ 0 :=
  eqToIso (by simp [presentationSource, Nat.not_le_of_lt h])

/-- The wedge map before descending through the presented quotient. -/
noncomputable def wedgeBeforeQuotient (r₁ r₀ : ℕ) (h : r₁ ≤ r₀) :
    (Λ[r₁] S.X₁) ⊗ (Λ[r₀ - r₁] S.X₂) ⟶ Λ[r₀] S.X₂ :=
  tensorHom (RingedSpace.ExteriorPower.map S.f r₁) (𝟙 _) ≫
    RingedSite.ExteriorPower.mul X.toRingedSpace.sheaf S.X₂ r₁ (r₀ - r₁) ≫
      eqToHom (congrArg (fun n ↦ Λ[n] S.X₂) (Nat.add_sub_of_le h))

/-- A short exact presentation induces an epimorphism on every exterior power of its quotient map. -/
theorem exteriorPowerMap_epi (hS : S.ShortExact) (n : ℕ) :
    Epi (RingedSpace.ExteriorPower.map S.g n) := sorry

/-- For a short exact presentation, the curried wedge map annihilates the kernel of the
exterior-power quotient map. -/
theorem kernelι_comp_curriedWedge
    (hS : S.ShortExact) (r₁ r₀ : ℕ) (h : r₁ ≤ r₀) :
    kernel.ι (RingedSpace.ExteriorPower.map S.g (r₀ - r₁)) ≫
      MonoidalClosed.curry (wedgeBeforeQuotient r₁ r₀ h) = 0 := sorry

/-- The canonical determinant map attached to a short exact finite locally free presentation.
Its target uses the closed-monoidal dual of the top exterior power of the first module, and its
source is zero when the virtual rank is negative. -/
noncomputable def presentationMap
    (hS : S.ShortExact) (r₁ r₀ : ℕ)
    [IsFiniteLocallyFreeOfRank r₁ S.X₁]
    [IsFiniteLocallyFreeOfRank r₀ S.X₂] :
    presentationSource S r₁ r₀ ⟶
      (MonoidalClosed.dual (Λ[r₁] S.X₁)) ⊗ (Λ[r₀] S.X₂) :=
  if h : r₁ ≤ r₀ then
    (presentationSourceIsoOfLE S r₁ r₀ h).hom ≫
      (let p := RingedSpace.ExteriorPower.map S.g (r₀ - r₁)
       let q := MonoidalClosed.curry (wedgeBeforeQuotient r₁ r₀ h)
       let descended :=
         @Abelian.epiDesc _ _ _ _ _ p
           (exteriorPowerMap_epi hS (r₀ - r₁)) _ q
           (kernelι_comp_curriedWedge hS r₁ r₀ h)
       let hComparison : IsIso
           (MonoidalClosed.Dual.tensorComparison (Λ[r₁] S.X₁) (Λ[r₀] S.X₂)) :=
         (@MonoidalCategory.isInvertibleObject.isRightDualizable
           _ _ _ (Λ[r₁] S.X₁)
           (RingedSite.ExteriorPower.top_isInvertible S.X₁ r₁)).isIso_tensorComparison
             (Λ[r₀] S.X₂)
       descended ≫
         @inv _ _ _ _ (MonoidalClosed.Dual.tensorComparison
           (Λ[r₁] S.X₁) (Λ[r₀] S.X₂)) hComparison ≫
           (β_ (Λ[r₀] S.X₂) (MonoidalClosed.dual (Λ[r₁] S.X₁))).hom)
  else
    0

/-- In nonnegative virtual rank, precomposing the determinant map with the exterior-power
quotient recovers the curried wedge construction after the tensor/internal-Hom comparison. -/
theorem presentationMap_spec
    (hS : S.ShortExact) (r₁ r₀ : ℕ) (h : r₁ ≤ r₀)
    [IsFiniteLocallyFreeOfRank r₁ S.X₁]
    [IsFiniteLocallyFreeOfRank r₀ S.X₂] :
    RingedSpace.ExteriorPower.map S.g (r₀ - r₁) ≫
        (presentationSourceIsoOfLE S r₁ r₀ h).inv ≫
          presentationMap hS r₁ r₀ ≫
            (β_ (Λ[r₀] S.X₂) (MonoidalClosed.dual (Λ[r₁] S.X₁))).inv ≫
              MonoidalClosed.Dual.tensorComparison (Λ[r₁] S.X₁) (Λ[r₀] S.X₂) =
      MonoidalClosed.curry (wedgeBeforeQuotient r₁ r₀ h) := sorry

/-- In negative virtual rank, the determinant map is the zero morphism under the canonical
identification of its source with the zero object. -/
theorem presentationMap_zero_of_lt
    (hS : S.ShortExact) (r₁ r₀ : ℕ) (h : r₀ < r₁)
    [IsFiniteLocallyFreeOfRank r₁ S.X₁]
    [IsFiniteLocallyFreeOfRank r₀ S.X₂] :
    (presentationSourceIsoZeroOfLT S r₁ r₀ h).inv ≫ presentationMap hS r₁ r₀ = 0 :=
  sorry

/-- The determinant map of a short exact finite locally free presentation is an isomorphism on
the stalk at a point exactly when the virtual rank is nonnegative and the presented module is
finite locally free of that rank on a neighborhood of the point. -/
theorem presentationMap_stalk_isIso_iff
    (hS : S.ShortExact) (r₁ r₀ : ℕ)
    [IsFiniteLocallyFreeOfRank r₁ S.X₁]
    [IsFiniteLocallyFreeOfRank r₀ S.X₂] (x : X) :
    IsIso (RingedSpace.moduleStalkHom x (presentationMap hS r₁ r₀)) ↔
      r₁ ≤ r₀ ∧
        ∃ (U : TopologicalSpace.Opens X) (_ : x ∈ U),
          IsFiniteLocallyFreeOfRank (r₀ - r₁) (S.X₃.over U) := sorry

end AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant
