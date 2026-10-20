/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra.Infinitesimal
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Operations
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass

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

noncomputable section

/-- The slice projection of the residue slice satisfies the Rim–Schlessinger condition. -/
instance instHasRimSchlessinger_deformationForget
    (P : FiniteProjectiveGradedAlgebra k) :
    HasRimSchlessinger (deformationForget Λ P) := sorry

/-- The underlying algebra of a dual-number fibre object, as a `k[ε]`-algebra via the fibre
identification of its base. -/
def fiberAlgebraMap (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (dualNumber Λ k).carrier →+* x.1.left.algebra.carrier :=
  (algebraMap x.1.left.base.carrier x.1.left.algebra.carrier).comp
    (eqToHom x.property.symm).hom.toRingHom

/-- `fiberAlgebraMap` is the structure map of the fibre algebra after transporting the base
along the fibre equality. -/
theorem fiberAlgebraMap_eq (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    fiberAlgebraMap Λ P x =
      (algebraMap x.1.left.base.carrier x.1.left.algebra.carrier).comp
        (eqToHom x.property.symm).hom.toRingHom := rfl

/-- The reduction of a dual-number fibre object to `P`, as a ring homomorphism. -/
def reductionRingHom (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    x.1.left.algebra.carrier →+* P.carrier :=
  x.1.hom.gradedHom.toRingHom

/-- `reductionRingHom` is the underlying ring map of the graded structure morphism to `P`. -/
theorem reductionRingHom_eq (P : FiniteProjectiveGradedAlgebra k)
    (x : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    reductionRingHom Λ P x = x.1.hom.gradedHom.toRingHom := rfl

/-- The underlying algebra of the Rim–Schlessinger fibre product of two dual-number
deformations, as the ring pullback of their reductions to `P`. -/
abbrev baerSumPullbackCarrier (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) : Type u :=
  RingHom.pullback (reductionRingHom Λ P x) (reductionRingHom Λ P y)

/-- An element of `baerSumPullbackCarrier` is a pair of algebra elements with the same
reduction to `P`. -/
theorem baerSumPullbackCarrier_fst_eq_snd (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k))
    (z : baerSumPullbackCarrier Λ P x y) :
    reductionRingHom Λ P x
        (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) =
      reductionRingHom Λ P y
        (RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) := z.property

/-- The `k[ε] ×_k k[ε]`-algebra map on the pullback of two dual-number deformations,
acting componentwise through `fiberAlgebraMap`. -/
def baerSumPullbackRingHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier →+*
      baerSumPullbackCarrier Λ P x y := by
  let coordinates : (dualNumberSelfPullback Λ).carrier →
      x.1.left.algebra.carrier × y.1.left.algebra.carrier := fun pair ↦
    (fiberAlgebraMap Λ P x ((dualNumberSelfPullbackFst Λ).hom pair),
      fiberAlgebraMap Λ P y ((dualNumberSelfPullbackSnd Λ).hom pair))
  have laws : (∀ pair, coordinates pair ∈
      RingHom.pullback (reductionRingHom Λ P x) (reductionRingHom Λ P y)) ∧
      coordinates 1 = 1 ∧ (∀ left right, coordinates (left * right) = coordinates left * coordinates right) ∧
      coordinates 0 = 0 ∧ (∀ left right, coordinates (left + right) = coordinates left + coordinates right) := sorry
  exact
    { toFun := fun pair ↦ ⟨coordinates pair, laws.1 pair⟩
      map_one' := Subtype.ext laws.2.1
      map_mul' := fun left right ↦ Subtype.ext (laws.2.2.1 left right)
      map_zero' := Subtype.ext laws.2.2.2.1
      map_add' := fun left right ↦ Subtype.ext (laws.2.2.2.2 left right) }

/-- `baerSumPullbackRingHom` acts by the two `fiberAlgebraMap`s on the pair of dual-number
coefficients. -/
theorem baerSumPullbackRingHom_apply (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k))
    (p : (dualNumberSelfPullback Λ).carrier) :
    (baerSumPullbackRingHom Λ P x y p :
        x.1.left.algebra.carrier × y.1.left.algebra.carrier) =
      (fiberAlgebraMap Λ P x ((dualNumberSelfPullbackFst Λ).hom p),
        fiberAlgebraMap Λ P y ((dualNumberSelfPullbackSnd Λ).hom p)) := rfl

/-- The pullback of two dual-number deformations is a `k[ε] ×_k k[ε]`-algebra. -/
instance instAlgebra_baerSumPullbackCarrier (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    Algebra (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier
      (baerSumPullbackCarrier Λ P x y) :=
  (baerSumPullbackRingHom Λ P x y).toAlgebra

/-- The degree-`d` piece of the fibre product is the pullback of the two degree-`d` pieces. -/
def baerSumPullbackGrading (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    ℕ → Submodule (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier
      (baerSumPullbackCarrier Λ P x y) := by
  let homogeneous := fun degree (value : baerSumPullbackCarrier Λ P x y) ↦
    value.val.1 ∈ x.1.left.algebra.grading degree ∧ value.val.2 ∈ y.1.left.algebra.grading degree
  have laws : ∀ degree,
      (∀ left right, homogeneous degree left → homogeneous degree right → homogeneous degree (left + right)) ∧
      homogeneous degree 0 ∧
      (∀ scalar : (dualNumberSelfPullback Λ : ArtinianLocalAlgCat Λ k).carrier, ∀ value,
        homogeneous degree value → homogeneous degree (scalar • value)) := sorry
  exact fun degree ↦
    { carrier := {value | homogeneous degree value}
      add_mem' := fun hleft hright ↦ (laws degree).1 _ _ hleft hright
      zero_mem' := (laws degree).2.1
      smul_mem' := (laws degree).2.2 }

/-- Membership in a homogeneous piece of the fibre product is membership in both degree-`d`
pieces. -/
theorem mem_baerSumPullbackGrading (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) {d : ℕ}
    {z : baerSumPullbackCarrier Λ P x y} :
    z ∈ baerSumPullbackGrading Λ P x y d ↔
      RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z ∈
          x.1.left.algebra.grading d ∧
        RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z ∈
          y.1.left.algebra.grading d := Iff.rfl

/-- Decomposition of the fibre-product algebra into homogeneous pieces, pairing the
decompositions of the two factors. -/
def baerSumPullbackDecompose (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackCarrier Λ P x y →+
      DirectSum ℕ fun d ↦ baerSumPullbackGrading Λ P x y d := by
  have compatibility : ∀ value : baerSumPullbackCarrier Λ P x y, ∀ degree,
      reductionRingHom Λ P x
        (DirectSum.decompose x.1.left.algebra.grading value.val.1 degree) =
      reductionRingHom Λ P y
        (DirectSum.decompose y.1.left.algebra.grading value.val.2 degree) := sorry
  let pieces : (value : baerSumPullbackCarrier Λ P x y) →
      (degree : ℕ) → baerSumPullbackGrading Λ P x y degree := fun value degree ↦
    Subtype.mk
      (Subtype.mk
        ((DirectSum.decompose x.1.left.algebra.grading value.val.1 degree : x.1.left.algebra.carrier),
          (DirectSum.decompose y.1.left.algebra.grading value.val.2 degree : y.1.left.algebra.carrier))
        (compatibility value degree))
      ⟨(DirectSum.decompose x.1.left.algebra.grading value.val.1 degree).property,
        (DirectSum.decompose y.1.left.algebra.grading value.val.2 degree).property⟩
  let components : baerSumPullbackCarrier Λ P x y →
      DirectSum ℕ fun degree ↦ baerSumPullbackGrading Λ P x y degree := fun value ↦
    let left := DirectSum.decompose x.1.left.algebra.grading value.val.1
    let right := DirectSum.decompose y.1.left.algebra.grading value.val.2
    let finiteSupport : Trunc {support : Multiset ℕ // ∀ degree, degree ∈ support ∨ pieces value degree = 0} :=
      left.support'.bind fun leftSupport ↦ right.support'.map fun rightSupport ↦
        ⟨leftSupport.val + rightSupport.val, fun degree ↦ by
          rcases leftSupport.property degree with hleft | hleft
          · exact Or.inl (Multiset.mem_add.mpr (Or.inl hleft))
          · rcases rightSupport.property degree with hright | hright
            · exact Or.inl (Multiset.mem_add.mpr (Or.inr hright))
            · right
              apply Subtype.ext
              apply Subtype.ext
              change ((left degree : x.1.left.algebra.carrier), (right degree : y.1.left.algebra.carrier)) = (0, 0)
              exact Prod.ext (congrArg Subtype.val hleft) (congrArg Subtype.val hright)⟩
    DFinsupp.mk' (pieces value) finiteSupport
  exact
    { toFun := components
      map_zero' := by
        apply DFinsupp.ext
        intro degree
        apply Subtype.ext
        apply Subtype.ext
        simp [components, pieces]
      map_add' := by
        intro left right
        apply DFinsupp.ext
        intro degree
        apply Subtype.ext
        apply Subtype.ext
        simp [components, pieces] }

/-- The degree-`d` component of `baerSumPullbackDecompose` is the pair of degree-`d`
components of the two factors. -/
theorem baerSumPullbackDecompose_apply (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k))
    (z : baerSumPullbackCarrier Λ P x y) (d : ℕ) :
    ((baerSumPullbackDecompose Λ P x y z d : baerSumPullbackCarrier Λ P x y) :
        x.1.left.algebra.carrier × y.1.left.algebra.carrier) =
      ((DirectSum.decompose x.1.left.algebra.grading
          (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) d :
          x.1.left.algebra.carrier),
        (DirectSum.decompose y.1.left.algebra.grading
          (RingHom.pullbackSnd (reductionRingHom Λ P x) (reductionRingHom Λ P y) z) d :
          y.1.left.algebra.carrier)) := sorry

/-- The pullback of two internally graded dual-number deformations is internally graded. -/
instance instGradedAlgebra_baerSumPullbackGrading (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    GradedAlgebra (baerSumPullbackGrading Λ P x y) := by
  have laws : (1 : baerSumPullbackCarrier Λ P x y) ∈ baerSumPullbackGrading Λ P x y 0 ∧
      (∀ degree otherDegree, ∀ left right : baerSumPullbackCarrier Λ P x y,
        left ∈ baerSumPullbackGrading Λ P x y degree →
        right ∈ baerSumPullbackGrading Λ P x y otherDegree →
        left * right ∈ baerSumPullbackGrading Λ P x y (degree + otherDegree)) ∧
      Function.LeftInverse (DirectSum.coeAddMonoidHom (baerSumPullbackGrading Λ P x y))
        (baerSumPullbackDecompose Λ P x y) ∧
      Function.RightInverse (DirectSum.coeAddMonoidHom (baerSumPullbackGrading Λ P x y))
        (baerSumPullbackDecompose Λ P x y) := sorry
  exact
    { one_mem := laws.1
      mul_mem := fun {degree otherDegree left right} hleft hright ↦
        laws.2.1 degree otherDegree left right hleft hright
      decompose' := baerSumPullbackDecompose Λ P x y
      left_inv := laws.2.2.1
      right_inv := laws.2.2.2 }

/-- Each homogeneous piece of the fibre product is finite projective over `k[ε] ×_k k[ε]`. -/
instance instIsFiniteProjective_baerSumPullbackGrading
    (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    IsFiniteProjective (baerSumPullbackGrading Λ P x y) := sorry

/-- The pair `(k[ε] ×_k k[ε], Q ×_P R)` as an object of `F`. -/
def baerSumPullbackObj (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    FiniteProjectiveGradedAlgebraCat Λ k :=
  of (dualNumberSelfPullback Λ)
    (FiniteProjectiveGradedAlgebra.of
      (baerSumPullbackCarrier Λ P x y) (baerSumPullbackGrading Λ P x y))

/-- The base of `baerSumPullbackObj` is the dual-number self-pullback. -/
theorem baerSumPullbackObj_base (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (baerSumPullbackObj Λ P x y).base = dualNumberSelfPullback Λ := rfl

/-- The reduction `Q ×_P R → P` of the fibre-product algebra, as a graded ring map. -/
def baerSumPullbackGradedHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackGrading Λ P x y →+*ᵍ P.grading := by
  let hom := (reductionRingHom Λ P x).comp
    (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y))
  have preservation : ∀ degree value, value ∈ baerSumPullbackGrading Λ P x y degree →
      hom value ∈ P.grading degree := sorry
  exact { toRingHom := hom, map_mem := fun {degree value} hvalue ↦ preservation degree value hvalue }

/-- The underlying ring map of `baerSumPullbackGradedHom` is the first pullback projection
followed by the reduction of `x`. -/
theorem baerSumPullbackGradedHom_toRingHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (baerSumPullbackGradedHom Λ P x y).toRingHom =
      (reductionRingHom Λ P x).comp
        (RingHom.pullbackFst (reductionRingHom Λ P x) (reductionRingHom Λ P y)) := rfl

/-- The morphism `(k[ε] ×_k k[ε], Q ×_P R) ⟶ (k, P)` over the coefficient projection. -/
def baerSumPullbackToResidue (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackObj Λ P x y ⟶ ofResidue Λ P := by
  let base : (baerSumPullbackObj Λ P x y).base ⟶ (ofResidue Λ P).base :=
    dualNumberSelfPullbackToResidue Λ
  let graded : (baerSumPullbackObj Λ P x y).algebra.grading →+*ᵍ (ofResidue Λ P).algebra.grading :=
    baerSumPullbackGradedHom Λ P x y
  have laws : graded.toRingHom.comp
      (algebraMap (baerSumPullbackObj Λ P x y).base.carrier (baerSumPullbackObj Λ P x y).algebra.carrier) =
      (algebraMap (ofResidue Λ P).base.carrier (ofResidue Λ P).algebra.carrier).comp
        (ArtinianLocalAlgCat.Hom.toRingHom base) ∧
      ∀ compatibility : graded.toRingHom.comp
        (algebraMap (baerSumPullbackObj Λ P x y).base.carrier (baerSumPullbackObj Λ P x y).algebra.carrier) =
        (algebraMap (ofResidue Λ P).base.carrier (ofResidue Λ P).algebra.carrier).comp
          (ArtinianLocalAlgCat.Hom.toRingHom base),
        Function.Bijective (canonicalTensorMap (Q := baerSumPullbackObj Λ P x y)
          (P := ofResidue Λ P) base graded compatibility) := sorry
  exact Hom.of base graded laws.1 (laws.2 laws.1)

/-- `baerSumPullbackToResidue` has base arrow `dualNumberSelfPullbackToResidue`. -/
theorem baerSumPullbackToResidue_baseHom (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (baerSumPullbackToResidue Λ P x y).baseHom =
      dualNumberSelfPullbackToResidue Λ := rfl

/-- The Rim–Schlessinger fibre product of two dual-number fibre objects of the residue slice, as the
graded algebra pullback of their underlying algebras along the reductions to `P`, lying over
`k[ε] ×_k k[ε]`. -/
def baerSumPullback (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    Over (Fiber.fiberInclusion.obj (residueObj Λ P)) :=
  Over.mk (baerSumPullbackToResidue Λ P x y)

/-- `baerSumPullback` is the over-object of `baerSumPullbackToResidue`. -/
theorem baerSumPullback_eq (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullback Λ P x y = Over.mk (baerSumPullbackToResidue Λ P x y) := rfl

/-- The fibre-product object of the residue slice over `k[ε] ×_k k[ε]`. -/
def baerSumPullbackFiber (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (deformationForget Λ P).Fiber (dualNumberSelfPullback Λ) :=
  Fiber.mk
    (rfl : (deformationForget Λ P).obj (baerSumPullback Λ P x y) = dualNumberSelfPullback Λ)

/-- `baerSumPullbackFiber` is the fibre object associated to `baerSumPullback`. -/
theorem baerSumPullbackFiber_eq (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumPullbackFiber Λ P x y =
      Fiber.mk
        (rfl : (deformationForget Λ P).obj (baerSumPullback Λ P x y) =
          dualNumberSelfPullback Λ) := rfl

/-- Baer sum of dual-number fibre objects: form the graded algebra fibre product over `x0`
and push forward along dual-number addition. -/
def baerSumFiber (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    (deformationForget Λ P).Fiber (dualNumber Λ k) :=
  pushforwardFiberObj (deformationForget Λ P) (cleavageOp (deformationForget Λ P))
    (dualNumberAddHom Λ) (baerSumPullbackFiber Λ P x y)

/-- `baerSumFiber` is the pushforward of the (RS) fibre product along dual-number addition. -/
theorem baerSumFiber_spec (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    baerSumFiber Λ P x y =
      pushforwardFiberObj (deformationForget Λ P) (cleavageOp (deformationForget Λ P))
        (dualNumberAddHom Λ) (baerSumPullbackFiber Λ P x y) := rfl

/-- Addition of tangent vectors by Baer sum of dual-number fibre classes. -/
def addTangent (P : FiniteProjectiveGradedAlgebra k) :
    tangentSpace (deformationForget Λ P) →
      tangentSpace (deformationForget Λ P) →
      tangentSpace (deformationForget Λ P) := by
  let addition := fun left right ↦
    tangentSpace.mk (deformationForget Λ P) (baerSumFiber Λ P left right)
  have descent : ∀ left right otherLeft otherRight,
      Nonempty (left ≅ otherLeft) → Nonempty (right ≅ otherRight) →
      addition left right = addition otherLeft otherRight := sorry
  exact Quotient.lift₂ addition descent

/-- `addTangent` on represented classes is the class of `baerSumFiber`. -/
theorem addTangent_eq (P : FiniteProjectiveGradedAlgebra k)
    (x y : (deformationForget Λ P).Fiber (dualNumber Λ k)) :
    addTangent Λ P (tangentSpace.mk (deformationForget Λ P) x)
        (tangentSpace.mk (deformationForget Λ P) y) =
      tangentSpace.mk (deformationForget Λ P) (baerSumFiber Λ P x y) := rfl

/-- Scalar multiplication on the tangent space by dual-number pushforward along `ε ↦ c ε`. -/
def smulTangent (P : FiniteProjectiveGradedAlgebra k) (c : k)
    (x : tangentSpace (deformationForget Λ P)) :
    tangentSpace (deformationForget Λ P) :=
  (pushforwardFiberFunctor (deformationForget Λ P) (cleavageOp (deformationForget Λ P))
      (dualNumberScaleHom Λ c)).isoClassesMap x

/-- `smulTangent` is pushforward of isomorphism classes along dual-number scaling. -/
theorem smulTangent_eq (P : FiniteProjectiveGradedAlgebra k) (c : k)
    (x : tangentSpace (deformationForget Λ P)) :
    smulTangent Λ P c x =
      (pushforwardFiberFunctor (deformationForget Λ P)
          (cleavageOp (deformationForget Λ P))
          (dualNumberScaleHom Λ c)).isoClassesMap x := rfl

/-- Zero tangent vector, as the class of the trivial deformation `P[ε]`. -/
instance instZero_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Zero (tangentSpace (deformationForget Λ P)) where
  zero := tangentSpace.mk (deformationForget Λ P) (trivialDeformationFiber Λ P)

/-- Addition of tangent vectors. -/
instance instAdd_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Add (tangentSpace (deformationForget Λ P)) where
  add := addTangent Λ P

/-- Negation of tangent vectors by scaling with `-1`. -/
instance instNeg_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Neg (tangentSpace (deformationForget Λ P)) where
  neg x := smulTangent Λ P (-1) x

/-- Additive group structure on the tangent space, with Baer sum as addition. -/
instance instAddCommGroup_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    AddCommGroup (tangentSpace (deformationForget Λ P)) := by
  let tangent := tangentSpace (deformationForget Λ P)
  have laws : (∀ left right third : tangent, left + right + third = left + (right + third)) ∧
      (∀ value : tangent, 0 + value = value) ∧ (∀ value : tangent, value + 0 = value) ∧
      (∀ value : tangent, -value + value = 0) ∧ (∀ left right : tangent, left + right = right + left) := sorry
  exact
    { add_assoc := laws.1
      zero_add := laws.2.1
      add_zero := laws.2.2.1
      nsmul := nsmulRec
      nsmul_zero := fun _ ↦ rfl
      nsmul_succ := fun _ _ ↦ rfl
      sub := fun left right ↦ left + -right
      sub_eq_add_neg := fun _ _ ↦ rfl
      zsmul := zsmulRec
      zsmul_zero' := fun _ ↦ rfl
      zsmul_succ' := fun _ _ ↦ rfl
      zsmul_neg' := fun _ _ ↦ rfl
      neg_add_cancel := laws.2.2.2.1
      add_comm := laws.2.2.2.2 }

/-- the tangent space is a `k`-vector space, with scalars acting by dual-number pushforward. -/
instance instModule_tangentSpace (P : FiniteProjectiveGradedAlgebra k) :
    Module k (tangentSpace (deformationForget Λ P)) := by
  let tangent := tangentSpace (deformationForget Λ P)
  have laws : (∀ value : tangent, smulTangent Λ P 1 value = value) ∧
      (∀ value : tangent, smulTangent Λ P 0 value = 0) ∧
      (∀ scalar : k, smulTangent Λ P scalar 0 = 0) ∧
      (∀ scalar : k, ∀ left right : tangent,
        smulTangent Λ P scalar (left + right) = smulTangent Λ P scalar left + smulTangent Λ P scalar right) ∧
      (∀ left right : k, ∀ value : tangent,
        smulTangent Λ P (left + right) value = smulTangent Λ P left value + smulTangent Λ P right value) ∧
      (∀ left right : k, ∀ value : tangent,
        smulTangent Λ P (left * right) value = smulTangent Λ P left (smulTangent Λ P right value)) := sorry
  exact
    { smul := smulTangent Λ P
      one_smul := laws.1
      zero_smul := laws.2.1
      smul_zero := laws.2.2.1
      smul_add := laws.2.2.2.1
      add_smul := laws.2.2.2.2.1
      mul_smul := laws.2.2.2.2.2 }

/-- The tangent space of a finite-type locally finite graded algebra is finite-dimensional. -/
instance tangentSpace_finiteDimensional (P : FiniteProjectiveGradedAlgebra k)
    [Algebra.FiniteType k P.carrier] :
    FiniteDimensional k (tangentSpace (deformationForget Λ P)) := sorry

end

end FiniteProjectiveGradedAlgebraCat
