/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Even
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»
public import stacks_project.Chap64.Definition_64_18_8_Cohomology
public import stacks_project.Chap64.Definition_64_19_1_EulerFactor
public import stacks_project.Chap64.Theorem_64_3_9_GaloisAction

/-!
# Cohomological Euler factors of Q_ℓ-sheaves

Compactly supported geometric cohomology `H_c^i(X_k̄, F)`, geometric Frobenius
`π_X^*`, and the signed reverse characteristic series in `PowerSeries ℚ_[ℓ]`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry Polynomial

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : ZEllSheaf X.left ℓ)

/-- Extension by zero of a stage along the interior of a `k`-compactification. -/
def compactificationExtensionByZeroStage (n : ℕ) :
    Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u} :=
  (etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u}).obj (F.stage n)

/-- Unfolding of extension by zero of a stage. -/
theorem compactificationExtensionByZeroStage_eq (n : ℕ) :
    compactificationExtensionByZeroStage P F n =
      (etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u}).obj
        (F.stage n) :=
  sorry

/-- Compactly supported cohomology of a stage on the geometric fibre, as
`H^i(Ȳ_k̄, (j_! F_n)|_{Ȳ_k̄})`. -/
def geometricStageCohomologyCompactSupport (n i : ℕ) : AddCommGrpCat.{u} :=
  geometricEtaleHq P.obj.right (compactificationExtensionByZeroStage P F n) i

/-- Unfolding of stagewise geometric compactly supported cohomology. -/
theorem geometricStageCohomologyCompactSupport_eq (n i : ℕ) :
    geometricStageCohomologyCompactSupport P F n i =
      geometricEtaleHq P.obj.right (compactificationExtensionByZeroStage P F n) i :=
  sorry

/-- Inverse system of geometric compactly supported cohomology of the stages. -/
def geometricCohomologyCompactSupportSystem (i : ℕ) :
    SequentialInverseSystem AddCommGrpCat.{u} where
  obj n := geometricStageCohomologyCompactSupport P F n.unop i
  map f :=
    (Sheaf.functorH
          (FieldExtension.baseChange k (AlgebraicClosure k)
            P.obj.right.hom).smallEtaleTopology i).map
      ((etaleAbelianSheafPullback
            (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).map
        ((etaleExtensionByZero (Compactification.Of.ι P) AddCommGrpCat.{u}).map
          (F.system.map f)))
  map_id := sorry
  map_comp := sorry

/-- Stage `n` of the geometric compactly supported cohomology inverse system is
`H_c^i(X_k̄, F.stage n)`. -/
theorem geometricCohomologyCompactSupportSystem_obj (i n : ℕ) :
    (geometricCohomologyCompactSupportSystem P F i).obj (op n) =
      geometricStageCohomologyCompactSupport P F n i :=
  sorry

/-- Compactly supported ℓ-adic cohomology `H_c^i(X_k̄, F)` as an inverse limit of
geometric stage cohomology. -/
def geometricCohomologyCompactSupport (i : ℕ) : AddCommGrpCat.{u} :=
  limit (geometricCohomologyCompactSupportSystem P F i)

/-- Unfolding of geometric compactly supported cohomology as an inverse limit. -/
theorem geometricCohomologyCompactSupport_eq (i : ℕ) :
    geometricCohomologyCompactSupport P F i =
      limit (geometricCohomologyCompactSupportSystem P F i) :=
  sorry

/-- Scalar-multiplication components by a `ℤ_[ℓ]`-integer on geometric compactly
supported cohomology. -/
def geometricCohomologyCompactSupportSMulπ (i : ℕ) (a : ℤ_[ℓ]) :
    (Functor.const ℕᵒᵖ).obj (geometricCohomologyCompactSupport P F i) ⟶
      geometricCohomologyCompactSupportSystem P F i where
  app n :=
    (PadicInt.toZModPow (n.unop + 1) a).val •
      limit.π (geometricCohomologyCompactSupportSystem P F i) n
  naturality := sorry

/-- Unfolding of the scalar-multiplication components on geometric compactly
supported cohomology. -/
theorem geometricCohomologyCompactSupportSMulπ_app (i : ℕ) (a : ℤ_[ℓ]) (n : ℕᵒᵖ) :
    (geometricCohomologyCompactSupportSMulπ P F i a).app n =
      (PadicInt.toZModPow (n.unop + 1) a).val •
        limit.π (geometricCohomologyCompactSupportSystem P F i) n :=
  sorry

/-- The cone presenting scalar multiplication on geometric compactly supported
cohomology. -/
def geometricCohomologyCompactSupportSMulCone (i : ℕ) (a : ℤ_[ℓ]) :
    Cone (geometricCohomologyCompactSupportSystem P F i) where
  pt := geometricCohomologyCompactSupport P F i
  π := geometricCohomologyCompactSupportSMulπ P F i a

/-- Unfolding of the scalar-multiplication cone on geometric compactly supported
cohomology. -/
theorem geometricCohomologyCompactSupportSMulCone_π (i : ℕ) (a : ℤ_[ℓ]) :
    (geometricCohomologyCompactSupportSMulCone P F i a).π =
      geometricCohomologyCompactSupportSMulπ P F i a :=
  sorry

/-- The endomorphism of geometric compactly supported cohomology given by scalar
multiplication by a `ℤ_[ℓ]`-integer. -/
def geometricCohomologyCompactSupportSMulHom (i : ℕ) (a : ℤ_[ℓ]) :
    geometricCohomologyCompactSupport P F i ⟶ geometricCohomologyCompactSupport P F i :=
  limit.lift (geometricCohomologyCompactSupportSystem P F i)
    (geometricCohomologyCompactSupportSMulCone P F i a)

/-- Unfolding of scalar multiplication on geometric compactly supported
cohomology as an inverse-limit lift. -/
theorem geometricCohomologyCompactSupportSMulHom_eq (i : ℕ) (a : ℤ_[ℓ]) :
    geometricCohomologyCompactSupportSMulHom P F i a =
      limit.lift (geometricCohomologyCompactSupportSystem P F i)
        (geometricCohomologyCompactSupportSMulCone P F i a) :=
  sorry

/-- The `ℤ_[ℓ]`-module structure on geometric compactly supported cohomology. -/
instance instModule_geometricCohomologyCompactSupport (i : ℕ) :
    Module ℤ_[ℓ] (geometricCohomologyCompactSupport P F i) where
  smul a y := geometricCohomologyCompactSupportSMulHom P F i a y
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Geometric compactly supported cohomology as a `ℤ_[ℓ]`-module. -/
def geometricCohomologyCompactSupportModule (i : ℕ) : ModuleCat.{u} ℤ_[ℓ] :=
  ModuleCat.of ℤ_[ℓ] (geometricCohomologyCompactSupport P F i)

/-- Unfolding of module-valued geometric compactly supported cohomology. -/
theorem geometricCohomologyCompactSupportModule_eq (i : ℕ) :
    geometricCohomologyCompactSupportModule P F i =
      ModuleCat.of ℤ_[ℓ] (geometricCohomologyCompactSupport P F i) :=
  sorry

/-- Compactly supported cohomology `H_c^i(X_k̄, F ⊗ ℚ_[ℓ])`, as extension of
scalars from `ℤ_[ℓ]` to `ℚ_[ℓ]`. -/
def geometricCohomologyCompactSupportQEll (i : ℕ) : ModuleCat.{u} ℚ_[ℓ] :=
  (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
    (geometricCohomologyCompactSupportModule P F i)

/-- Unfolding of geometric `ℚ_[ℓ]` compactly supported cohomology as extension of
scalars. -/
theorem geometricCohomologyCompactSupportQEll_eq (i : ℕ) :
    geometricCohomologyCompactSupportQEll P F i =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (geometricCohomologyCompactSupport P F i)) :=
  sorry

/-- Geometric compactly supported `ℚ_[ℓ]`-cohomology is finite-dimensional. -/
instance instFiniteDimensional_geometricCohomologyCompactSupportQEll (i : ℕ) :
    FiniteDimensional ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) :=
  sorry

/-- Geometric compactly supported `ℚ_[ℓ]`-cohomology is a projective module. -/
instance instProjective_geometricCohomologyCompactSupportQEll (i : ℕ) :
    Module.Projective ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) :=
  inferInstance

/-- The cone presenting geometric Frobenius on the inverse system of geometric
compactly supported cohomology, as Galois action of `frob_k⁻¹`. -/
def geometricFrobenius_cohomologyCompactSupportCone (i : ℕ) :
    Cone (geometricCohomologyCompactSupportSystem P F i) where
  pt := geometricCohomologyCompactSupport P F i
  π :=
    { app := fun n ↦
        limit.π (geometricCohomologyCompactSupportSystem P F i) n ≫
          galoisEtaleHq P.obj.right
            (compactificationExtensionByZeroStage P F n.unop) i
            (FiniteField.arithmeticFrobenius k)⁻¹
      naturality := sorry }

/-- The cone projection of geometric Frobenius is inverse-limit projection
followed by Galois action of `frob_k⁻¹`. -/
theorem geometricFrobenius_cohomologyCompactSupportCone_π_app (i : ℕ) (n : ℕᵒᵖ) :
    (geometricFrobenius_cohomologyCompactSupportCone P F i).π.app n =
      limit.π (geometricCohomologyCompactSupportSystem P F i) n ≫
        galoisEtaleHq P.obj.right
          (compactificationExtensionByZeroStage P F n.unop) i
          (FiniteField.arithmeticFrobenius k)⁻¹ :=
  sorry

/-- Geometric Frobenius on geometric compactly supported `ℤ_[ℓ]`-cohomology, as
the inverse-limit of the Galois action of `frob_k⁻¹`. -/
def geometricFrobenius_cohomologyCompactSupportZEllHom (i : ℕ) :
    geometricCohomologyCompactSupport P F i ⟶ geometricCohomologyCompactSupport P F i :=
  limit.lift (geometricCohomologyCompactSupportSystem P F i)
    (geometricFrobenius_cohomologyCompactSupportCone P F i)

/-- Unfolding of geometric Frobenius on `ℤ_[ℓ]`-cohomology as an inverse-limit
lift. -/
theorem geometricFrobenius_cohomologyCompactSupportZEllHom_eq (i : ℕ) :
    geometricFrobenius_cohomologyCompactSupportZEllHom P F i =
      limit.lift (geometricCohomologyCompactSupportSystem P F i)
        (geometricFrobenius_cohomologyCompactSupportCone P F i) :=
  sorry

/-- Geometric Frobenius as a `ℤ_[ℓ]`-linear endomorphism of `H_c^i(X_k̄, F)`. -/
def geometricFrobenius_cohomologyCompactSupportZEll (i : ℕ) :
    Module.End ℤ_[ℓ] (geometricCohomologyCompactSupport P F i) where
  toFun := geometricFrobenius_cohomologyCompactSupportZEllHom P F i
  map_add' := sorry
  map_smul' := sorry

/-- Geometric Frobenius on `H_c^i(X_k̄, F)` applies as the inverse-limit Galois
action of `frob_k⁻¹`. -/
theorem geometricFrobenius_cohomologyCompactSupportZEll_apply (i : ℕ)
    (x : geometricCohomologyCompactSupport P F i) :
    geometricFrobenius_cohomologyCompactSupportZEll P F i x =
      geometricFrobenius_cohomologyCompactSupportZEllHom P F i x :=
  sorry

/-- Geometric Frobenius `π_X^*` on `H_c^i(X_k̄, F ⊗ ℚ_[ℓ])`, as extension of
scalars of the inverse-limit Galois action of `frob_k⁻¹`. -/
def geometricFrobenius_cohomologyCompactSupportQEll (i : ℕ) :
    Module.End ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) :=
  ModuleCat.Hom.hom
    ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (ModuleCat.ofHom (geometricFrobenius_cohomologyCompactSupportZEll P F i)))

/-- Unfolding of `π_X^*` as extension of scalars of the `ℤ_[ℓ]`-linear inverse-limit
Galois action. -/
theorem geometricFrobenius_cohomologyCompactSupportQEll_spec (i : ℕ) :
    geometricFrobenius_cohomologyCompactSupportQEll P F i =
      ModuleCat.Hom.hom
        ((ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (ModuleCat.ofHom (geometricFrobenius_cohomologyCompactSupportZEll P F i))) :=
  sorry

/-- The cohomological Euler factor `det(1 - π_X^* T | H_c^i(X_k̄, F))` in
`PowerSeries ℚ_[ℓ]`. -/
def cohomologyEulerFactor (i : ℕ) : PowerSeries ℚ_[ℓ] :=
  Polynomial.toPowerSeries
    (LinearMap.charpolyRev (geometricFrobenius_cohomologyCompactSupportQEll P F i))

/-- Unfolding of `cohomologyEulerFactor` as the reverse characteristic polynomial
of `π_X^*` on `H_c^i(X_k̄, F ⊗ ℚ_[ℓ])`. -/
theorem cohomologyEulerFactor_spec (i : ℕ) :
    cohomologyEulerFactor P F i =
      Polynomial.toPowerSeries
        (LinearMap.charpolyRev
          (geometricFrobenius_cohomologyCompactSupportQEll P F i)) :=
  sorry

/-- The constant coefficient of each cohomological Euler factor is `1`. -/
theorem constantCoeff_cohomologyEulerFactor (i : ℕ) :
    PowerSeries.constantCoeff (cohomologyEulerFactor P F i) = 1 :=
  sorry

/-- The signed cohomological Euler factor
`det(1 - π_X^* T | H_c^i(X_k̄, F))^{(-1)^{i+1}}`. Even degrees are inverted. -/
def signedCohomologyEulerFactor (i : ℕ) : PowerSeries ℚ_[ℓ] :=
  if Even i then PowerSeries.invOfUnit (cohomologyEulerFactor P F i) 1
  else cohomologyEulerFactor P F i

/-- Unfolding of the signed cohomological Euler factor into the even (inverse)
and odd (uninverted) cases. -/
theorem signedCohomologyEulerFactor_spec (i : ℕ) :
    signedCohomologyEulerFactor P F i =
      if Even i then PowerSeries.invOfUnit (cohomologyEulerFactor P F i) 1
      else cohomologyEulerFactor P F i :=
  sorry

/-- The finite cohomological L-function
`∏_{i=0}^N det(1 - π_X^* T | H_c^i(X_k̄, F))^{(-1)^{i+1}}` in
`PowerSeries ℚ_[ℓ]`. -/
def cohomologicalLFunction (N : ℕ) : PowerSeries ℚ_[ℓ] :=
  ∏ i ∈ Finset.range (N + 1), signedCohomologyEulerFactor P F i

/-- Unfolding of `cohomologicalLFunction` as a finite product of signed
cohomological Euler factors. -/
theorem cohomologicalLFunction_spec (N : ℕ) :
    cohomologicalLFunction P F N =
      ∏ i ∈ Finset.range (N + 1), signedCohomologyEulerFactor P F i :=
  sorry

/-- Enlarging a vanishing bound does not change the cohomological L-function. -/
theorem cohomologicalLFunction_eq_of_vanishing {N M : ℕ} (hNM : N ≤ M)
    (hN : ∀ i, N < i →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) :
    cohomologicalLFunction P F N = cohomologicalLFunction P F M :=
  sorry

/-- The cohomological L-function is independent of the choice of compactification. -/
theorem cohomologicalLFunction_independent
    (Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι Q)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Compactification.Of.ι Q)).op.HasLeftKanExtension G]
    [HasWeakSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})]
    (N : ℕ) :
    cohomologicalLFunction P F N = cohomologicalLFunction Q F N :=
  sorry


end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
