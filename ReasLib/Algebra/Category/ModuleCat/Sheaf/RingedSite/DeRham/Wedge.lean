/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham.Wedge
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.NatMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Restriction
public import ReasLib.Algebra.Homology.ComplexShapeSigns.Nat
public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Component

/-!
# Wedge multiplication on relative de Rham complexes of ringed sites

The sectionwise wedge product is sheafified, restricted to the source scalars, and assembled via
the graded Leibniz rule into a morphism from the total tensor product of de Rham complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DeRham

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ : Sheaf J CommRingCat.{max u v}}

/-- The sheafification of the canonical presheaf wedge product on relative forms. -/
noncomputable def formWedge (φ : O₁ ⟶ O₂) (p q : ℕ) :
    moduleTensor (form φ p) (form φ q) ⟶ form φ (p + q) :=
  (ModuleSheafification.tensorIso O₂
      (PresheafOfModules.DeRham.form φ.hom p)
      (PresheafOfModules.DeRham.form φ.hom q)).hom ≫
    (moduleSheafification O₂).map
      (PresheafOfModules.DeRham.formWedge φ.hom p q)

/-- The sheaf wedge is induced by objectwise concatenation of relative forms. -/
theorem formWedge_def (φ : O₁ ⟶ O₂) (p q : ℕ) :
    formWedge φ p q =
      (ModuleSheafification.tensorIso O₂
          (PresheafOfModules.DeRham.form φ.hom p)
          (PresheafOfModules.DeRham.form φ.hom q)).hom ≫
        (moduleSheafification O₂).map
          (PresheafOfModules.DeRham.formWedge φ.hom p q) := sorry

/-- The degreewise wedge product after restricting scalars to the source ring sheaf. -/
noncomputable def wedgeComponent (φ : O₁ ⟶ O₂) (p q : ℕ) :
    moduleTensor (term φ p) (term φ q) ⟶ term φ (p + q) :=
  Restriction.tensorComparison φ (form φ p) (form φ q) ≫
    (restriction φ).map (formWedge φ p q)

/-- The canonical degreewise wedge satisfies the graded Leibniz rule. -/
theorem wedgeComponent_leibniz (φ : O₁ ⟶ O₂) (p q : ℕ) :
    wedgeComponent φ p q ≫ d φ (p + q) =
      (d φ p ▷ term φ q) ≫ wedgeComponent φ (p + 1) q ≫
          eqToHom (congrArg (term φ) (Nat.succ_add p q)) +
        ((-1 : ℤ) ^ p) •
          ((term φ p ◁ d φ q) ≫ wedgeComponent φ p (q + 1) ≫
            eqToHom (congrArg (term φ) (Nat.add_succ p q))) := sorry

/-- The canonical wedge morphism from the total tensor product of relative de Rham complexes. -/
noncomputable def wedge (φ : O₁ ⟶ O₂) :
    HomologicalComplex.tensorObj (complex φ) (complex φ) ⟶ complex φ where
  f n := HomologicalComplex.mapBifunctorDesc
    (K₁ := complex φ) (K₂ := complex φ)
    (F := curriedTensor (ringedSiteModuleCategory J O₁)) (c := up ℕ)
    fun p q h ↦ wedgeComponent φ p q ≫
      eqToHom (congrArg (complex φ).X h)
  comm' := sorry

/-- Every homogeneous component of `wedge` is the corresponding canonical exterior product. -/
theorem wedge_component (φ : O₁ ⟶ O₂) (p q : ℕ) :
    HomologicalComplex.Monoidal.tensorHomComponent (wedge φ) p q =
      wedgeComponent φ p q := sorry

end SheafOfModules.RingedSite.DeRham
