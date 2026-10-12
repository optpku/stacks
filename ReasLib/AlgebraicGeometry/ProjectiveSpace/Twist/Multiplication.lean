/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Associated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.Algebra.Module.Graded.Shift.NatInt

/-!
# Multiplication of twists on projective space

This file constructs multiplication of the canonical twisting sheaves on standard projective
space and the induced linear maps on global sections.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

set_option maxHeartbeats 1000000

/-- The homogeneous coordinate ring of standard projective `n`-space. -/
abbrev polynomialRing (R : Type u) [CommRing R] (n : ℕ) :=
  MvPolynomial (Fin (n + 1)) R

/-- The integer-indexed regular grading of the homogeneous coordinate ring of standard
projective space. -/
abbrev regularGrading (R : Type u) [CommRing R] (n : ℕ) :
    ℤ → Submodule ℤ (polynomialRing R n) :=
  fun i ↦ (DirectSum.Decomposition.natToIntGrading (grading R n) i).restrictScalars ℤ

/-- The additive restriction of the regular grading retains its canonical direct-sum
decomposition. -/
noncomputable instance regularGrading_decomposition
    (R : Type u) [CommRing R] (n : ℕ) :
    DirectSum.Decomposition (regularGrading R n) :=
  inferInstanceAs
    (DirectSum.Decomposition (DirectSum.Decomposition.natToIntGrading (grading R n)))

/-- The homogeneous-coordinate-ring action remains graded after restricting the regular
grading to integer scalars. -/
instance regularGrading_gradedSMul
    (R : Type u) [CommRing R] (n : ℕ) :
    SetLike.GradedSMul (grading R n) (regularGrading R n) where
  smul_mem := fun {_ _ _ _} ha hx ↦
    SetLike.GradedSMul.smul_mem
      (A := grading R n)
      (B := DirectSum.Decomposition.natToIntGrading (grading R n)) ha hx

/-- Translating the integer-scalar regular grading preserves the homogeneous-coordinate-ring
action. -/
instance shiftedRegularGrading_gradedSMul
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    SetLike.GradedSMul (grading R n)
      (GradedModule.shiftGrading (regularGrading R n) d) where
  smul_mem := fun {i j a x} ha hx ↦ by
    apply (GradedModule.mem_shiftGrading_iff (regularGrading R n) d _).mpr
    change a • x ∈ regularGrading R n (((i : ℤ) + j) + d)
    have hindex : ((i : ℤ) + j) + d = i +ᵥ (j + d) := by
      change ((i : ℤ) + j) + d = (i : ℤ) + (j + d)
      exact add_assoc _ _ _
    rw [hindex]
    exact SetLike.GradedSMul.smul_mem
      (A := grading R n) (B := regularGrading R n) ha
      ((GradedModule.mem_shiftGrading_iff (regularGrading R n) d _).mp hx)

/-- Restricting the scalar ring used to record the regular grading does not change its
associated twisting sheaf. -/
noncomputable def twistingSheafRestrictScalarsIso
    (R : Type u) [CommRing R] (n : ℕ) (d : ℤ) :
    twistingSheaf R n d ≅
      Proj.AssociatedModule.sheaf (grading R n)
        (GradedModule.shiftGrading (regularGrading R n) d) :=
  eqToIso (by rfl)

/-- Multiplication on the tensor product of two shifted regular gradings preserves total
degree, with the output shifted by the sum of the two indices. -/
theorem twistingSheafMul_mapsTo
    (R : Type u) [CommRing R] (n : ℕ) (a b i : ℤ) :
    Set.MapsTo
      (TensorProduct.lid (polynomialRing R n) (polynomialRing R n)).toLinearMap
      (GradedModule.TensorProduct.grading (polynomialRing R n)
        (GradedModule.shiftGrading (regularGrading R n) a)
        (GradedModule.shiftGrading (regularGrading R n) b) i)
      (GradedModule.shiftGrading (regularGrading R n) (a + b) i) := sorry

/-- Multiplication of the integer-scalar presentations of two shifted regular gradings. -/
noncomputable def twistingSheafMulRestricted
    (R : Type u) [CommRing R] (n : ℕ) (a b : ℤ) :
    (tensorObj
      (Proj.AssociatedModule.sheaf (grading R n)
        (GradedModule.shiftGrading (regularGrading R n) a))
      (Proj.AssociatedModule.sheaf (grading R n)
        (GradedModule.shiftGrading (regularGrading R n) b)) :
        (scheme R n).Modules) ⟶
      Proj.AssociatedModule.sheaf (grading R n)
        (GradedModule.shiftGrading (regularGrading R n) (a + b)) :=
  Proj.AssociatedModule.Tensor.hom (grading R n)
      (GradedModule.shiftGrading (regularGrading R n) a)
      (GradedModule.shiftGrading (regularGrading R n) b) ≫
    Proj.AssociatedModule.map (grading R n)
      (GradedModule.TensorProduct.gradingFor (polynomialRing R n) (grading R n)
        (GradedModule.shiftGrading (regularGrading R n) a)
        (GradedModule.shiftGrading (regularGrading R n) b))
      (GradedModule.shiftGrading (regularGrading R n) (a + b))
      (TensorProduct.lid (polynomialRing R n) (polynomialRing R n)).toLinearMap
      (twistingSheafMul_mapsTo R n a b)

/-- The canonical multiplication morphism `𝒶(a) ⊗ 𝒶(b) ⟶ 𝒶(a + b)` on
standard projective space. -/
noncomputable def twistingSheafMul
    (R : Type u) [CommRing R] (n : ℕ) (a b : ℤ) :
    (tensorObj (twistingSheaf R n a) (twistingSheaf R n b) :
      (scheme R n).Modules) ⟶ twistingSheaf R n (a + b) :=
  ((twistingSheafRestrictScalarsIso R n a).hom ⊗ₘ
      (twistingSheafRestrictScalarsIso R n b).hom) ≫
    twistingSheafMulRestricted R n a b ≫
      (twistingSheafRestrictScalarsIso R n (a + b)).inv

/-- Multiplication of twisting sheaves sends a pure tensor section to the associated section
obtained by multiplying the two shifted homogeneous fractions. -/
theorem twistingSheafMul_tensorSection
    (R : Type u) [CommRing R] (n : ℕ) (a b : ℤ)
    (U : ((scheme R n).Opens)ᵒᵖ)
    (x : (twistingSheaf R n a).val.obj U)
    (y : (twistingSheaf R n b).val.obj U) :
    (((twistingSheafMul R n a b).val.app U).hom)
        (SheafOfModules.RingedSite.tensorSection (scheme R n).sheaf U x y) =
      Proj.AssociatedModule.mapSection (grading R n)
        (GradedModule.TensorProduct.gradingFor (polynomialRing R n) (grading R n)
          (GradedModule.shiftGrading (regularGrading R n) a)
          (GradedModule.shiftGrading (regularGrading R n) b))
        (GradedModule.shiftGrading (regularGrading R n) (a + b))
        (TensorProduct.lid (polynomialRing R n) (polynomialRing R n)).toLinearMap
        (twistingSheafMul_mapsTo R n a b) U.unop
        (Proj.AssociatedModule.Tensor.sectionValue (grading R n)
          (GradedModule.shiftGrading (regularGrading R n) a)
          (GradedModule.shiftGrading (regularGrading R n) b) U.unop x y) := sorry

/-- Multiplication of a twist of `ℱ` by a twisting sheaf combines the two twist indices. -/
noncomputable def twistMul
    (R : Type u) [CommRing R] (n : ℕ) (ℱ : (scheme R n).Modules) (a b : ℤ) :
    (tensorObj (twist R n ℱ a) (twistingSheaf R n b) :
      (scheme R n).Modules) ⟶ twist R n ℱ (a + b) :=
  (α_ ℱ (twistingSheaf R n a) (twistingSheaf R n b)).hom ≫
    (𝟙 ℱ ⊗ₘ twistingSheafMul R n a b)

/-- The base-linear multiplication map
`H⁰(ℱ(a)) ⊗[R] H⁰(𝒶(b)) ⟶ H⁰(ℱ(a + b))` on standard projective space. -/
noncomputable def twistGlobalSectionsMul
    (R : Type u) [CommRing R] (n : ℕ) (ℱ : (scheme R n).Modules) (a b : ℤ) :
    Scheme.Hom.globalSectionsMod (toSpec R n) (twist R n ℱ a) ⊗[R]
        Scheme.Hom.globalSectionsMod (toSpec R n) (twistingSheaf R n b) →ₗ[R]
      Scheme.Hom.globalSectionsMod (toSpec R n) (twist R n ℱ (a + b)) := by
  -- Restrict the global-section ring along the fixed structure morphism `toSpec R n`.
  -- Local instance justification (defeq pin): align its `R`-algebra with `globalSectionsMod`.
  letI : Algebra R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u) :=
    Scheme.Hom.globalSectionsAlgebra (toSpec R n)
  -- The first source uses the scalar structure bundled by `globalSectionsMod`.
  -- Local instance justification (defeq pin): align that structure with the section module.
  letI : Module R ((twist R n ℱ a).val.obj (op ⊤) : Type u) :=
    Scheme.Hom.globalSectionsModule (toSpec R n) (twist R n ℱ a)
  -- The second source uses the scalar structure bundled by `globalSectionsMod`.
  -- Local instance justification (defeq pin): align that structure with the section module.
  letI : Module R ((twistingSheaf R n b).val.obj (op ⊤) : Type u) :=
    Scheme.Hom.globalSectionsModule (toSpec R n) (twistingSheaf R n b)
  -- Tensor-sheaf sections use the scalar restriction needed by the section-level bilinear map.
  -- Local instance justification (defeq pin): align that restriction with global sections.
  letI : Module R
      (((twist R n ℱ a ⊗ twistingSheaf R n b).val.obj (op ⊤)) : Type u) :=
    Scheme.Hom.globalSectionsModule (toSpec R n)
      (twist R n ℱ a ⊗ twistingSheaf R n b)
  -- The target uses the scalar structure bundled by `globalSectionsMod`.
  -- Local instance justification (defeq pin): align that structure with the section module.
  letI : Module R ((twist R n ℱ (a + b)).val.obj (op ⊤) : Type u) :=
    Scheme.Hom.globalSectionsModule (toSpec R n) (twist R n ℱ (a + b))
  -- The bilinear section map uses the native section-ring action on the first factor.
  -- Local instance justification (defeq pin): expose that action while restricting to `R`.
  letI : Module Γ(scheme R n, ⊤) Γ(twist R n ℱ a, ⊤) :=
    ((twist R n ℱ a).val.obj (op ⊤)).isModule
  -- The bilinear section map uses the native section-ring action on the second factor.
  -- Local instance justification (defeq pin): expose that action while restricting to `R`.
  letI : Module Γ(scheme R n, ⊤) Γ(twistingSheaf R n b, ⊤) :=
    ((twistingSheaf R n b).val.obj (op ⊤)).isModule
  -- The bilinear section map uses the native section-ring action on its tensor-sheaf target.
  -- Local instance justification (defeq pin): expose that action while restricting to `R`.
  letI : Module Γ(scheme R n, ⊤)
      Γ(twist R n ℱ a ⊗ twistingSheaf R n b, ⊤) :=
    ((twist R n ℱ a ⊗ twistingSheaf R n b).val.obj (op ⊤)).isModule
  -- The first factor's restricted module structure determines the required scalar tower.
  -- Local instance justification (proof-local temporary data): certify that tower for `lift`.
  letI : IsScalarTower R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u)
      ((twist R n ℱ a).val.obj (op ⊤) : Type u) :=
    IsScalarTower.of_compHom R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u) _
  -- The second factor's restricted module structure determines the required scalar tower.
  -- Local instance justification (proof-local temporary data): certify that tower for `lift`.
  letI : IsScalarTower R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u)
      ((twistingSheaf R n b).val.obj (op ⊤) : Type u) :=
    IsScalarTower.of_compHom R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u) _
  -- The tensor-sheaf target's restricted module structure determines the required scalar tower.
  -- Local instance justification (proof-local temporary data): certify that tower for `lift`.
  letI : IsScalarTower R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u)
      ((twist R n ℱ a ⊗ twistingSheaf R n b).val.obj (op ⊤) : Type u) :=
    IsScalarTower.of_compHom R ((scheme R n).sheaf.obj.obj (op ⊤) : Type u) _
  let tensorBilinear :
      ((twist R n ℱ a).val.obj (op ⊤) : Type u) →ₗ[R]
        ((twistingSheaf R n b).val.obj (op ⊤) : Type u) →ₗ[R]
          ((twist R n ℱ a ⊗ twistingSheaf R n b).val.obj (op ⊤) : Type u) :=
    LinearMap.restrictScalars₁₂ R R <|
      SheafOfModules.RingedSite.tensorSectionLinear (scheme R n).sheaf
        (twist R n ℱ a) (twistingSheaf R n b) (op ⊤)
  exact TensorProduct.lift <| tensorBilinear.compr₂
    ((Scheme.Hom.globalSectionsFunctor (toSpec R n)).map
      (twistMul R n ℱ a b)).hom

/-- The global-sections multiplication map evaluates on a pure tensor by taking the pure tensor
section and applying the twist multiplication morphism. -/
theorem twistGlobalSectionsMul_tmul
    (R : Type u) [CommRing R] (n : ℕ) (ℱ : (scheme R n).Modules) (a b : ℤ)
    (x : Scheme.Hom.globalSectionsMod (toSpec R n) (twist R n ℱ a))
    (y : Scheme.Hom.globalSectionsMod (toSpec R n) (twistingSheaf R n b)) :
    twistGlobalSectionsMul R n ℱ a b (x ⊗ₜ[R] y) =
      (((twistMul R n ℱ a b).val.app (op ⊤)).hom)
        (SheafOfModules.RingedSite.tensorSection (scheme R n).sheaf (op ⊤) x y) := sorry

/-- The base-linear multiplication map
`H⁰(ℱ(m)) ⊗[R] H⁰(𝒶(1)) ⟶ H⁰(ℱ(m + 1))` on standard projective space. -/
noncomputable def twistOneGlobalSectionsTensorMap
    (R : Type u) [CommRing R] (n : ℕ) (ℱ : (scheme R n).Modules) (m : ℤ) :
    Scheme.Hom.globalSectionsMod (toSpec R n) (twist R n ℱ m) ⊗[R]
        Scheme.Hom.globalSectionsMod (toSpec R n) (twistingSheaf R n 1) →ₗ[R]
      Scheme.Hom.globalSectionsMod (toSpec R n) (twist R n ℱ (m + 1)) :=
  twistGlobalSectionsMul R n ℱ m 1

end AlgebraicGeometry.ProjectiveSpace
