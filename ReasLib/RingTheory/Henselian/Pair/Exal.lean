module

public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Locus
public import ReasLib.RingTheory.Extension.SquareZero
public import ReasLib.RingTheory.Henselian.Pair.BaseChange

/-!
# Henselization of square-zero algebra extensions

Pair henselization of geometric square-zero extensions induces a map on
cotangent extension classes. For finite coefficients over a finite type
algebra over a field, smooth away from the distinguished closed subset,
this map is bijective.
-/

public section
noncomputable section
universe u

open Algebra Algebra.Generators Algebra.Extension CategoryTheory RingPairCat
open scoped TensorProduct

namespace Algebra.Exal

variable (B N : Type u) [CommRing B] [AddCommGroup N] [Module B N]

/-- The coefficient module `N ⊗[B] B^h` has the action transported from `B^h ⊗[B] N`. -/
instance instModule_tensor_henselizationRing (J : Ideal B) :
    Module (henselizationRing (pairOfIdeal J) : Type u)
      (N ⊗[B] (henselizationRing (pairOfIdeal J) : Type u)) :=
  (_root_.TensorProduct.comm B N
      (henselizationRing (pairOfIdeal J) : Type u)).toAddEquiv.module
    (henselizationRing (pairOfIdeal J) : Type u)

/-- Scalars on henselized coefficients multiply the right tensor factor. -/
theorem smul_tmul_henselizationRing (J : Ideal B) (n : N)
    (s t : henselizationRing (pairOfIdeal J)) :
    s • (n ⊗ₜ[B] t) = n ⊗ₜ[B] (s * t) := by
  change (_root_.TensorProduct.comm B N
    (henselizationRing (pairOfIdeal J) : Type u)).symm
      (s • (_root_.TensorProduct.comm B N
        (henselizationRing (pairOfIdeal J) : Type u)) (n ⊗ₜ[B] t)) = _
  simp only [_root_.TensorProduct.comm_tmul, _root_.TensorProduct.smul_tmul', smul_eq_mul,
    _root_.TensorProduct.comm_symm]

end Algebra.Exal

namespace Algebra.SquareZeroAlgExtension

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

private def henselizationPairHom (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  let I := Ideal.comap e.toB.toRingHom J
  pairOfIdeal I ⟶ pairOfIdeal J :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  let I := Ideal.comap e.toB.toRingHom J
  InducedCategory.homMk <|
    Arrow.homMk' (CommRingCat.ofHom e.toB.toRingHom)
      (CommRingCat.ofHom (Ideal.quotientMap J e.toB.toRingHom (le_rfl : I ≤ I)))
      (pairOfIdeal_hom_square_of_ringHom I J e.toB.toRingHom le_rfl)

private def henselizationProjectionRing (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  let I := Ideal.comap e.toB.toRingHom J
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  (henselizationRing (pairOfIdeal I) : Type u) →+* Bh :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  henselizationRingMap (henselizationPairHom e J)

private theorem henselization_projection_commutes
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  let I := Ideal.comap e.toB.toRingHom J
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  ∀ a : A, henselizationProjectionRing e J
      (algebraMap A (henselizationRing (pairOfIdeal I)) a) = algebraMap A Bh a :=
  sorry

private def henselizationProjection (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  let I := Ideal.comap e.toB.toRingHom J
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  (henselizationRing (pairOfIdeal I) : Type u) →ₐ[A] Bh :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  { toRingHom := henselizationProjectionRing e J
    commutes' := by exact henselization_projection_commutes e J }

private theorem henselization_projection_isSquareZero
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
  sorry

private theorem henselization_cotangentUnit_mem
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I := Ideal.comap e.toB.toRingHom J
  ∀ y : Ideal.Cotangent (RingHom.ker e.toB.toRingHom),
    toHenselization (pairOfIdeal I)
      ((RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).symm y).1 ∈
        RingHom.ker (henselizationProjection e J).toRingHom :=
  sorry

private def henselizationCotangentUnitValue
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  Ideal.Cotangent (RingHom.ker e.toB.toRingHom) →
    Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let I := Ideal.comap e.toB.toRingHom J
  fun y ↦ Ideal.toCotangent _
    ⟨toHenselization (pairOfIdeal I)
      ((RingHom.SquareZeroExtension.toCotangentEquiv_source e.toB.toRingHom).symm y).1,
      by exact henselization_cotangentUnit_mem e J y⟩

private theorem henselization_cotangentUnit_add
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  ∀ x y : Ideal.Cotangent (RingHom.ker e.toB.toRingHom),
    henselizationCotangentUnitValue e J (x + y) =
      henselizationCotangentUnitValue e J x + henselizationCotangentUnitValue e J y :=
  sorry

private theorem henselization_cotangentUnit_smul
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  ∀ (r : B) (x : Ideal.Cotangent (RingHom.ker e.toB.toRingHom)),
    henselizationCotangentUnitValue e J (r • x) =
      r • henselizationCotangentUnitValue e J x :=
  sorry

private def henselizationCotangentUnit
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  Ideal.Cotangent (RingHom.ker e.toB.toRingHom) →ₗ[B]
    Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  { toFun := henselizationCotangentUnitValue e J
    map_add' := by exact henselization_cotangentUnit_add e J
    map_smul' := by exact henselization_cotangentUnit_smul e J }

private def henselizationTensorUnit
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  -- Local instance justification (proof-local temporary data): restriction of scalars gives the tower for base change.
  letI : IsScalarTower B Bh
      (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    IsScalarTower.of_compHom B Bh _
  Ideal.Cotangent (RingHom.ker e.toB.toRingHom) ⊗[B] Bh →ₗ[B]
    Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  -- Local instance justification (proof-local temporary data): restriction of scalars gives the tower for base change.
  letI : IsScalarTower B Bh
      (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    IsScalarTower.of_compHom B Bh _
  ((henselizationCotangentUnit e J).liftBaseChange Bh).restrictScalars B ∘ₗ
    (_root_.TensorProduct.comm B (Ideal.Cotangent (RingHom.ker e.toB.toRingHom)) Bh).toLinearMap

private theorem henselization_tensorUnit_bijective
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  Function.Bijective (henselizationTensorUnit e J) :=
  sorry

private def henselizationKernelEquiv
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom) ≃ₗ[B]
    N ⊗[B] Bh :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  (LinearEquiv.ofBijective (henselizationTensorUnit e J)
    (by exact henselization_tensorUnit_bijective e J)).symm.trans
      (_root_.TensorProduct.congr e.kernelEquiv (LinearEquiv.refl B Bh))

private theorem henselization_kernelMap_smul
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  ∀ (s : Bh) (x : Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)),
    henselizationKernelEquiv e J (s • x) = s • henselizationKernelEquiv e J x :=
  sorry

private def henselizationKernelMap
    (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom) →ₗ[Bh]
    N ⊗[B] Bh :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the algebra projection requires the stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  { toFun := henselizationKernelEquiv e J
    map_add' := (henselizationKernelEquiv e J).map_add
    map_smul' := by exact henselization_kernelMap_smul e J }

/-- Henselizing the middle ring along the inverse image of `J` gives an extension
of `B^h` by `N ⊗[B] B^h`. -/
def henselization (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
    SquareZeroAlgExtension A (henselizationRing (pairOfIdeal J) : Type u)
      (N ⊗[B] (henselizationRing (pairOfIdeal J) : Type u)) :=
  -- Local instance justification (proof-local temporary data): unpack the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack its stored base algebra.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack its stored square-zero projection.
  letI := e.isSquareZero
  let Bh := (henselizationRing (pairOfIdeal J) : Type u)
  -- Local instance justification (proof-local temporary data): the induced projection is square-zero.
  letI : (henselizationProjection e J).toRingHom.IsSquareZeroExtension :=
    by exact henselization_projection_isSquareZero e J
  -- Local instance justification (proof-local temporary data): restrict the target cotangent action along B → B^h.
  letI : Module B (Ideal.Cotangent (RingHom.ker (henselizationProjection e J).toRingHom)) :=
    Module.compHom _ (algebraMap B Bh)
  of (henselizationProjection e J)
    (LinearEquiv.ofBijective (henselizationKernelMap e J) (henselizationKernelEquiv e J).bijective)

/-- The middle ring of a henselized extension is the henselization of its middle ring
along the inverse image of the distinguished ideal. -/
theorem henselization_carrier (e : SquareZeroAlgExtension A B N) (J : Ideal B) :
  -- Local instance justification (proof-local temporary data): the inverse-image ideal uses the stored middle ring.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): the projection uses the stored algebra.
  letI := e.algebra
  (e.henselization J).carrier =
    (henselizationRing (pairOfIdeal (Ideal.comap e.toB.toRingHom J)) : Type u) := by rfl

end Algebra.SquareZeroAlgExtension

namespace Algebra.Exal

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

private theorem henselization_respects (J : Ideal B)
    (f g : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (h : (LinearMap.range (LinearMap.lcomp B N
      (Generators.self A B).toExtension.cotangentComplex)).quotientRel f g) :
    SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).henselization J) =
      SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom g).henselization J) := sorry

/-- Pair henselization induces a map on first-order algebra extension classes. -/
def henselization (J : Ideal B) :
    Exal A B N →
      Exal A (henselizationRing (pairOfIdeal J) : Type u)
        (N ⊗[B] (henselizationRing (pairOfIdeal J) : Type u)) :=
  fun x ↦ Quotient.liftOn x
    (fun f ↦ SquareZeroAlgExtension.toClass ((SquareZeroAlgExtension.ofHom f).henselization J))
    (by exact henselization_respects A B N J)

/-- Henselizing a conormal representative gives the class of its henselized realization. -/
theorem henselization_mk (J : Ideal B)
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    henselization A B N J (mk A B N f) =
      SquareZeroAlgExtension.toClass
        ((SquareZeroAlgExtension.ofHom f).henselization J) := by rfl

/-- Henselization of the class of any geometric extension is the class of its henselization. -/
theorem henselization_toClass (J : Ideal B) (e : SquareZeroAlgExtension A B N) :
    henselization A B N J e.toClass = (e.henselization J).toClass := sorry

/-- For finite coefficients over a finite type algebra over a field, smooth off the
closed subset defined by an ideal, pair henselization is bijective on extension classes. -/
theorem henselization_bijective (k B N : Type u) [Field k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N] [Algebra.FiniteType k B] [Module.Finite B N]
    (J : Ideal B)
    (hsmooth : (PrimeSpectrum.zeroLocus (J : Set B))ᶜ ⊆ Algebra.smoothLocus k B) :
    Function.Bijective (henselization k B N J) := sorry

end Algebra.Exal
