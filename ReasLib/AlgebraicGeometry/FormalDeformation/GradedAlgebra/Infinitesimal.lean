/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousDerivations
public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Section
public import ReasLib.RingTheory.DualNumber.Derivation

@[expose] public section

open CategoryTheory Functor
open ArtinianLocalAlgCat
open TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (Λ)

open GradedAlgebra

namespace FiniteProjectiveGradedAlgebraCat

/-- The projection from the residue slice of graded algebras to its Artinian local base. -/
abbrev deformationForget (P : FiniteProjectiveGradedAlgebra k) :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget

/-- `deformationForget Λ P` is the composite of the Over-forgetful functor with `forget`. -/
theorem deformationForget_eq (P : FiniteProjectiveGradedAlgebra k) :
    deformationForget Λ P =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget := rfl

/-- The slice projection of the residue slice is a predeformation category. -/
instance instIsPredeformationCategory_deformationForget
    (P : FiniteProjectiveGradedAlgebra k) :
    IsPredeformationCategory (deformationForget Λ P) := sorry

/-- Predeformation categories are cofibered in groupoids. -/
instance instIsFiberedInGroupoids_deformationForget_op
    (P : FiniteProjectiveGradedAlgebra k) :
    IsFibered.InGroupoids (deformationForget Λ P).op :=
  IsPredeformationCategory.isCofiberedInGroupoids

/-- The canonical `k[ε]`-algebra structure on `P[ε] = DualNumber P.carrier`. -/
def dualNumberRingHom (P : FiniteProjectiveGradedAlgebra k) :
    DualNumber k →+* DualNumber P.carrier := by
  let coefficients : DualNumber k → DualNumber P.carrier :=
    fun value ↦ ⟨algebraMap k P.carrier value.fst, algebraMap k P.carrier value.snd⟩
  have laws : coefficients 1 = 1 ∧
      (∀ left right, coefficients (left * right) = coefficients left * coefficients right) ∧
      coefficients 0 = 0 ∧
      (∀ left right, coefficients (left + right) = coefficients left + coefficients right) := sorry
  exact
    { toFun := coefficients
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2 }

/-- `P[ε]` is a `k[ε]`-algebra via the coefficientwise algebra map. -/
instance instAlgebra_dualNumber (P : FiniteProjectiveGradedAlgebra k) :
    Algebra (dualNumber Λ k).carrier (DualNumber P.carrier) :=
  (dualNumberRingHom P).toAlgebra

/-- The degree-`d` piece of `P[ε]` is `P_d ⊕ ε P_d`. -/
def trivialDeformationGrading (P : FiniteProjectiveGradedAlgebra k) :
    ℕ → Submodule (dualNumber Λ k).carrier (DualNumber P.carrier) := by
  have laws : ∀ degree,
      (∀ left right : DualNumber P.carrier,
        (left.fst ∈ P.grading degree ∧ left.snd ∈ P.grading degree) →
        (right.fst ∈ P.grading degree ∧ right.snd ∈ P.grading degree) →
        (left + right).fst ∈ P.grading degree ∧ (left + right).snd ∈ P.grading degree) ∧
      ((0 : DualNumber P.carrier).fst ∈ P.grading degree ∧
        (0 : DualNumber P.carrier).snd ∈ P.grading degree) ∧
      (∀ scalar : (dualNumber Λ k).carrier, ∀ value : DualNumber P.carrier,
        (value.fst ∈ P.grading degree ∧ value.snd ∈ P.grading degree) →
        (scalar • value).fst ∈ P.grading degree ∧ (scalar • value).snd ∈ P.grading degree) := sorry
  exact fun degree ↦
    { carrier := {value | value.fst ∈ P.grading degree ∧ value.snd ∈ P.grading degree}
      add_mem' := fun hleft hright ↦ (laws degree).1 _ _ hleft hright
      zero_mem' := (laws degree).2.1
      smul_mem' := (laws degree).2.2 }

/-- Inclusion of a homogeneous summand as the scalar part of `P[ε]`. -/
def gradingFstEmbed (P : FiniteProjectiveGradedAlgebra k) (d : ℕ) :
    P.grading d →+ trivialDeformationGrading Λ P d := by
  let inclusion : P.grading d → DualNumber P.carrier := fun value ↦ ⟨(value : P.carrier), 0⟩
  have laws : (∀ value, inclusion value ∈ trivialDeformationGrading Λ P d) ∧
      inclusion 0 = 0 ∧
      (∀ left right, inclusion (left + right) = inclusion left + inclusion right) := sorry
  exact
    { toFun := fun value ↦ ⟨inclusion value, laws.1 value⟩
      map_zero' := Subtype.ext laws.2.1
      map_add' := fun left right ↦ Subtype.ext (laws.2.2 left right) }

/-- Inclusion of a homogeneous summand as the `ε`-part of `P[ε]`. -/
def gradingSndEmbed (P : FiniteProjectiveGradedAlgebra k) (d : ℕ) :
    P.grading d →+ trivialDeformationGrading Λ P d := by
  let inclusion : P.grading d → DualNumber P.carrier := fun value ↦ ⟨0, (value : P.carrier)⟩
  have laws : (∀ value, inclusion value ∈ trivialDeformationGrading Λ P d) ∧
      inclusion 0 = 0 ∧
      (∀ left right, inclusion (left + right) = inclusion left + inclusion right) := sorry
  exact
    { toFun := fun value ↦ ⟨inclusion value, laws.1 value⟩
      map_zero' := Subtype.ext laws.2.1
      map_add' := fun left right ↦ Subtype.ext (laws.2.2 left right) }

/-- Decomposition of `P[ε]` into homogeneous pieces, induced by the decomposition of `P`. -/
def trivialDecompose (P : FiniteProjectiveGradedAlgebra k) :
    DualNumber P.carrier →+ DirectSum ℕ fun d ↦ trivialDeformationGrading Λ P d := by
  let decomposition : DualNumber P.carrier → DirectSum ℕ fun degree ↦ trivialDeformationGrading Λ P degree :=
    fun value ↦
      DirectSum.map (gradingFstEmbed Λ P) (DirectSum.decompose P.grading value.fst) +
        DirectSum.map (gradingSndEmbed Λ P) (DirectSum.decompose P.grading value.snd)
  have laws : decomposition 0 = 0 ∧
      (∀ left right, decomposition (left + right) = decomposition left + decomposition right) := sorry
  exact { toFun := decomposition, map_zero' := laws.1, map_add' := laws.2 }

/-- The grading `P_d ⊕ ε P_d` makes `P[ε]` an internally graded `k[ε]`-algebra. -/
instance instGradedAlgebra_trivialDeformationGrading (P : FiniteProjectiveGradedAlgebra k) :
    GradedAlgebra (trivialDeformationGrading Λ P) := by
  have laws :
      (1 : DualNumber P.carrier) ∈ trivialDeformationGrading Λ P 0 ∧
      (∀ degree otherDegree, ∀ left right : DualNumber P.carrier,
        left ∈ trivialDeformationGrading Λ P degree →
        right ∈ trivialDeformationGrading Λ P otherDegree →
        left * right ∈ trivialDeformationGrading Λ P (degree + otherDegree)) ∧
      Function.LeftInverse (DirectSum.coeAddMonoidHom (trivialDeformationGrading Λ P))
        (trivialDecompose Λ P) ∧
      Function.RightInverse (DirectSum.coeAddMonoidHom (trivialDeformationGrading Λ P))
        (trivialDecompose Λ P) := sorry
  exact
    { one_mem := laws.1
      mul_mem := fun {degree otherDegree left right} hleft hright ↦
        laws.2.1 degree otherDegree left right hleft hright
      decompose' := trivialDecompose Λ P
      left_inv := laws.2.2.1
      right_inv := laws.2.2.2 }

/-- Each homogeneous piece of `P[ε]` is finite projective over `k[ε]`. -/
instance instIsFiniteProjective_trivialDeformationGrading
    (P : FiniteProjectiveGradedAlgebra k) :
    IsFiniteProjective (trivialDeformationGrading Λ P) := sorry

/-- The trivial dual-number deformation `Q = P ⊗_k k[ε]`, realized as `P[ε]`. -/
def trivialDeformation (P : FiniteProjectiveGradedAlgebra k) :
    FiniteProjectiveGradedAlgebraCat Λ k :=
  of (dualNumber Λ k)
    (FiniteProjectiveGradedAlgebra.of (DualNumber P.carrier) (trivialDeformationGrading Λ P))

/-- The base of the trivial deformation is `k[ε]`. -/
theorem trivialDeformation_base (P : FiniteProjectiveGradedAlgebra k) :
    (trivialDeformation Λ P).base = dualNumber Λ k := rfl

/-- The underlying algebra of the trivial deformation is `DualNumber P.carrier`. -/
theorem trivialDeformation_carrier (P : FiniteProjectiveGradedAlgebra k) :
    (trivialDeformation Λ P).algebra.carrier = DualNumber P.carrier := rfl

/-- The projection `P[ε] → P`, `(a, b) ↦ a`, as a graded ring homomorphism. -/
def trivialDeformationProj (P : FiniteProjectiveGradedAlgebra k) :
    trivialDeformationGrading Λ P →+*ᵍ P.grading := by
  let hom := (fstHom k P.carrier P.carrier).toRingHom
  have preservation : ∀ degree value, value ∈ trivialDeformationGrading Λ P degree → hom value ∈ P.grading degree := sorry
  exact { toRingHom := hom, map_mem := fun {degree value} hvalue ↦ preservation degree value hvalue }

/-- The inclusion `P → P[ε]`, `a ↦ (a, 0)`, as a graded ring homomorphism. -/
def trivialDeformationIncl (P : FiniteProjectiveGradedAlgebra k) :
    P.grading →+*ᵍ trivialDeformationGrading Λ P := by
  let hom := inlHom P.carrier P.carrier
  have preservation : ∀ degree value, value ∈ P.grading degree → hom value ∈ trivialDeformationGrading Λ P degree := sorry
  exact { toRingHom := hom, map_mem := fun {degree value} hvalue ↦ preservation degree value hvalue }

/-- The morphism `(k[ε], P[ε]) ⟶ (k, P)` over the coefficient projection `k[ε] ⟶ k`. -/
def trivialDeformationToResidue (P : FiniteProjectiveGradedAlgebra k) :
    trivialDeformation Λ P ⟶ ofResidue Λ P := by
  let base : (trivialDeformation Λ P).base ⟶ (ofResidue Λ P).base := ArtinianLocalAlgCat.dualNumberToResidue Λ k
  let graded : (trivialDeformation Λ P).algebra.grading →+*ᵍ (ofResidue Λ P).algebra.grading := trivialDeformationProj Λ P
  have laws : graded.toRingHom.comp (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier) =
      (algebraMap (ofResidue Λ P).base.carrier (ofResidue Λ P).algebra.carrier).comp (ArtinianLocalAlgCat.Hom.toRingHom base) ∧
      ∀ compatibility : graded.toRingHom.comp (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier) =
        (algebraMap (ofResidue Λ P).base.carrier (ofResidue Λ P).algebra.carrier).comp (ArtinianLocalAlgCat.Hom.toRingHom base),
        Function.Bijective (canonicalTensorMap (Q := trivialDeformation Λ P) (P := ofResidue Λ P) base graded compatibility) := sorry
  exact Hom.of base graded laws.1 (laws.2 laws.1)

/-- The morphism `(k, P) ⟶ (k[ε], P[ε])` over the inclusion `k ⟶ k[ε]`. -/
def residueToTrivialDeformation (P : FiniteProjectiveGradedAlgebra k) :
    ofResidue Λ P ⟶ trivialDeformation Λ P := by
  let base : (ofResidue Λ P).base ⟶ (trivialDeformation Λ P).base := ArtinianLocalAlgCat.residueToDualNumber Λ k
  let graded : (ofResidue Λ P).algebra.grading →+*ᵍ (trivialDeformation Λ P).algebra.grading := trivialDeformationIncl Λ P
  have laws : graded.toRingHom.comp (algebraMap (ofResidue Λ P).base.carrier (ofResidue Λ P).algebra.carrier) =
      (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier).comp (ArtinianLocalAlgCat.Hom.toRingHom base) ∧
      ∀ compatibility : graded.toRingHom.comp (algebraMap (ofResidue Λ P).base.carrier (ofResidue Λ P).algebra.carrier) =
        (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier).comp (ArtinianLocalAlgCat.Hom.toRingHom base),
        Function.Bijective (canonicalTensorMap (Q := ofResidue Λ P) (P := trivialDeformation Λ P) base graded compatibility) := sorry
  exact Hom.of base graded laws.1 (laws.2 laws.1)

/-- The trivial deformation as an object of the residue-fibre slice the residue slice. -/
def trivialDeformationOver (P : FiniteProjectiveGradedAlgebra k) :
    Over (Fiber.fiberInclusion.obj (residueObj Λ P)) :=
  Over.mk (trivialDeformationToResidue Λ P)

/-- The identity object of the residue slice, lying over the residue field. -/
def deformationResidueOver (P : FiniteProjectiveGradedAlgebra k) :
    Over (Fiber.fiberInclusion.obj (residueObj Λ P)) :=
  Over.mk (𝟙 (Fiber.fiberInclusion.obj (residueObj Λ P)))

/-- The trivial deformation in the dual-number fibre of `deformationForget`. -/
def trivialDeformationFiber (P : FiniteProjectiveGradedAlgebra k) :
    (deformationForget Λ P).Fiber (dualNumber Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ P).obj (trivialDeformationOver Λ P) = dualNumber Λ k)

/-- The identity object of the residue slice in the residue fibre of `deformationForget`. -/
def deformationResidueFiber (P : FiniteProjectiveGradedAlgebra k) :
    (deformationForget Λ P).Fiber (residue Λ k) :=
  Fiber.mk
    (rfl : (deformationForget Λ P).obj (deformationResidueOver Λ P) = residue Λ k)

/-- `id + ε D` as a graded endomorphism of `P[ε]`. The map preserves the grading
`P_d ⊕ ε P_d` precisely when `D` is homogeneous of degree 0. -/
def idAddEpsilonGradedHom (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) :
    trivialDeformationGrading Λ P →+*ᵍ trivialDeformationGrading Λ P := by
  let hom := (DualNumber.autOfDerivation D.val).toRingHom
  have preservation : ∀ degree value, value ∈ trivialDeformationGrading Λ P degree → hom value ∈ trivialDeformationGrading Λ P degree := sorry
  exact { toRingHom := hom, map_mem := fun {degree value} hvalue ↦ preservation degree value hvalue }

/-- `id + ε D` as an endomorphism of the trivial deformation in the graded-algebra category. -/
def idAddEpsilonHom (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) :
    trivialDeformation Λ P ⟶ trivialDeformation Λ P := by
  let base : (trivialDeformation Λ P).base ⟶ (trivialDeformation Λ P).base := 𝟙 (dualNumber Λ k)
  let graded : (trivialDeformation Λ P).algebra.grading →+*ᵍ (trivialDeformation Λ P).algebra.grading := idAddEpsilonGradedHom Λ P D
  have laws : graded.toRingHom.comp (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier) =
      (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier).comp (ArtinianLocalAlgCat.Hom.toRingHom base) ∧
      ∀ compatibility : graded.toRingHom.comp (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier) =
        (algebraMap (trivialDeformation Λ P).base.carrier (trivialDeformation Λ P).algebra.carrier).comp (ArtinianLocalAlgCat.Hom.toRingHom base),
        Function.Bijective (canonicalTensorMap (Q := trivialDeformation Λ P) (P := trivialDeformation Λ P) base graded compatibility) := sorry
  exact Hom.of base graded laws.1 (laws.2 laws.1)

/-- `id + ε D` as an automorphism of the trivial deformation in the dual-number fibre of
the residue slice, associated to a homogeneous degree-zero derivation. -/
def idAddEpsilon (P : FiniteProjectiveGradedAlgebra k)
    (D : homogeneousDerivations P.grading) :
    Aut (trivialDeformationFiber Λ P) := by
  let forward := idAddEpsilonHom Λ P D
  let backward := idAddEpsilonHom Λ P (-D)
  have laws :
      forward ≫ trivialDeformationToResidue Λ P = trivialDeformationToResidue Λ P ∧
      backward ≫ trivialDeformationToResidue Λ P = trivialDeformationToResidue Λ P ∧
      forward.baseHom = 𝟙 (dualNumber Λ k) ∧
      backward.baseHom = 𝟙 (dualNumber Λ k) ∧
      forward ≫ backward = 𝟙 (trivialDeformation Λ P) ∧
      backward ≫ forward = 𝟙 (trivialDeformation Λ P) := sorry
  exact
    { hom := ⟨Over.homMk forward laws.1, by
        apply IsHomLift.of_fac (ha := rfl) (hb := rfl)
        change 𝟙 (dualNumber Λ k) = forward.baseHom
        exact laws.2.2.1.symm⟩
      inv := ⟨Over.homMk backward laws.2.1, by
        apply IsHomLift.of_fac (ha := rfl) (hb := rfl)
        change 𝟙 (dualNumber Λ k) = backward.baseHom
        exact laws.2.2.2.1.symm⟩
      hom_inv_id := by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        exact laws.2.2.2.2.1
      inv_hom_id := by
        apply Subtype.ext
        apply Over.OverMorphism.ext
        exact laws.2.2.2.2.2 }

/-- The comparison `γ = id + ε D` is a monoid homomorphism from homogeneous derivations
to fibre automorphisms of `P[ε]`. -/
theorem idAddEpsilon_map_add (P : FiniteProjectiveGradedAlgebra k)
    (D E : homogeneousDerivations P.grading) :
    idAddEpsilon Λ P (D + E) = idAddEpsilon Λ P D * idAddEpsilon Λ P E := sorry

/-- Every automorphism of the trivial graded deformation over the dual numbers is uniquely
induced by a degree-preserving derivation. -/
theorem inf_bijective_homogeneousDerivations (P : FiniteProjectiveGradedAlgebra k) :
    Function.Bijective (idAddEpsilon Λ P) := sorry


end FiniteProjectiveGradedAlgebraCat
