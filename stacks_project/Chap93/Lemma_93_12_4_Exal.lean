/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Extension.Generators
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# First-order square-zero algebra extensions

`Algebra.Exal A B N` is the source model of Ext¹_B(NL_{B/A}, N): Hom_B of the
conormal module of the self-presentation A[B] → B, modulo maps that factor
through the free cotangent space. Geometric representatives are bundled as
`Algebra.SquareZeroAlgExtension`.
-/

@[expose] public section

noncomputable section

universe u

open Algebra Algebra.Generators Algebra.Extension
open TrivSqZeroExt

namespace Algebra

variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- The opposite action of a commutative ring on a module. -/
@[reducible]
def moduleMulOpposite (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M] :
    Module Rᵐᵒᵖ M :=
  Module.compHom M ((RingHom.id R).fromOpposite fun x y ↦ mul_comm x y)

/-- Left and opposite actions of a commutative ring on a module agree. -/
theorem moduleMulOpposite_smul_eq_smul (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] (r : R) (x : M) :
    -- Local instance justification (instance diamond): opposite-module action is local to this equality; a global `Module Rᵐᵒᵖ M` instance diamonds.
    letI := moduleMulOpposite R M
    MulOpposite.op r • x = r • x := sorry

/-- Centrality of the opposite action of a commutative ring on a module. -/
theorem isCentralScalar_of_commRing (R M : Type u) [CommRing R] [AddCommGroup M]
    [Module R M] :
    -- Local instance justification (instance diamond): opposite-module action is local to this centrality witness; a global `Module Rᵐᵒᵖ M` instance diamonds.
    letI := moduleMulOpposite R M
    IsCentralScalar R M :=
  -- Local instance justification (instance diamond): opposite-module action is local to this centrality witness; a global `Module Rᵐᵒᵖ M` instance diamonds.
  letI := moduleMulOpposite R M
  ⟨moduleMulOpposite_smul_eq_smul R M⟩

/-- Restriction of scalars of an `S`-module along an algebra map. -/
@[reducible]
def moduleRestrictScalars (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] : Module R M :=
  Module.compHom M (algebraMap R S)

/-- Cotangent of the kernel of a square-zero surjection, as a module over the target. -/
instance instModule_cotangent_of_squareZero {C B : Type u} [CommRing C] [CommRing B]
    (f : C →+* B) [h : f.IsSquareZeroExtension] :
    Module B (Ideal.Cotangent (RingHom.ker f)) :=
  Module.compHom _ (f.quotientKerEquivOfSurjective h.surjective).symm.toRingHom

/-- First-order algebra extensions of `B` by `N` over `A`, as Ext¹_B(NL_{B/A}, N). -/
abbrev Exal : Type u :=
  let P := (Generators.self A B).toExtension
  (P.Cotangent →ₗ[B] N) ⧸ LinearMap.range (LinearMap.lcomp B N P.cotangentComplex)

namespace Exal

/-- The class of a `B`-linear map out of the self-presentation conormal module. -/
def mk (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) : Exal A B N :=
  Submodule.Quotient.mk f

/-- Unfolding of `Exal.mk`. -/
theorem mk_def (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    mk A B N f = Submodule.Quotient.mk f := sorry

/-- A class vanishes iff some representative factors through the cotangent space. -/
theorem mk_eq_zero_iff (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    mk A B N f = 0 ↔
      ∃ g : (Generators.self A B).toExtension.CotangentSpace →ₗ[B] N,
        f = g ∘ₗ (Generators.self A B).toExtension.cotangentComplex := sorry

/-- Equality of classes is membership of the difference in the cotangent range. -/
theorem mk_eq_mk (f g : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    mk A B N f = mk A B N g ↔
      f - g ∈ LinearMap.range
        (LinearMap.lcomp B N (Generators.self A B).toExtension.cotangentComplex) :=
  sorry

end Exal

/-- A geometric square-zero `A`-algebra extension `0 → N → C → B → 0`. -/
structure SquareZeroAlgExtension where
  /-- The middle ring of the extension. -/
  carrier : Type u
  /-- Commutative ring structure on the middle term. -/
  [commRing : CommRing carrier]
  /-- The structure map `A → carrier`. -/
  [algebra : Algebra A carrier]
  /-- The square-zero surjection onto `B`. -/
  toB : carrier →ₐ[A] B
  /-- The projection is a square-zero extension. -/
  [isSquareZero : toB.toRingHom.IsSquareZeroExtension]
  /-- `B`-linear identification of the conormal of the kernel with `N`. -/
  kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N

namespace SquareZeroAlgExtension

variable {A B N}

/-- Assemble a square-zero algebra extension from a middle ring, a square-zero
surjection onto `B`, and a kernel identification. -/
def of {C : Type u} [CommRing C] [Algebra A C] (toB : C →ₐ[A] B)
    [hsq : toB.toRingHom.IsSquareZeroExtension]
    (kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N) :
    SquareZeroAlgExtension A B N where
  carrier := C
  commRing := inferInstance
  algebra := inferInstance
  toB := toB
  isSquareZero := hsq
  kernelEquiv := kernelEquiv

/-- The middle ring of `of` is the supplied carrier. -/
theorem of_carrier {C : Type u} [CommRing C] [Algebra A C] (toB : C →ₐ[A] B)
    [toB.toRingHom.IsSquareZeroExtension]
    (kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N) :
    (of toB kernelEquiv).carrier = C := sorry

/-- The projection of `of` is the supplied algebra map. -/
theorem of_toB {C : Type u} [CommRing C] [Algebra A C] (toB : C →ₐ[A] B)
    [toB.toRingHom.IsSquareZeroExtension]
    (kernelEquiv : Ideal.Cotangent (RingHom.ker toB.toRingHom) ≃ₗ[B] N) :
    (of toB kernelEquiv).toB = toB := sorry

/-- The split square-zero extension `TrivSqZeroExt B N`. -/
def triv : SquareZeroAlgExtension A B N :=
  -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `Module Bᵐᵒᵖ N`; a global opposite-module instance on raw types diamonds.
  letI := moduleMulOpposite B N
  -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `IsCentralScalar B N`; a global centrality instance on raw types diamonds.
  letI := isCentralScalar_of_commRing B N
  -- Local instance justification (proof-local temporary data): restrict scalars along `algebraMap A B` so `TrivSqZeroExt.algebra'` can elaborate.
  letI := moduleRestrictScalars A B N
  -- Local instance justification (proof-local temporary data): scalar tower for `TrivSqZeroExt.algebra'` along `A → B`.
  letI : IsScalarTower A B N := ⟨fun _ _ _ ↦ sorry⟩
  -- Local instance justification (proof-local temporary data): opposite scalar tower for `TrivSqZeroExt.algebra'`.
  letI : IsScalarTower A Bᵐᵒᵖ N := ⟨fun _ _ _ ↦ sorry⟩
  -- Local instance justification (instance diamond): `SMulCommClass` for the opposite action used by `TrivSqZeroExt.algebra'`.
  letI : SMulCommClass B Bᵐᵒᵖ N := ⟨fun _ _ _ ↦ sorry⟩
  -- Local instance justification (proof-local temporary data): `fstHom` is the split square-zero projection, not a global instance on `AlgHom`.
  letI : (fstHom A B N).toRingHom.IsSquareZeroExtension := ⟨sorry, sorry⟩
  of (fstHom A B N)
    (LinearEquiv.ofBijective
      { toFun := fun x : Ideal.Cotangent (RingHom.ker (fstHom A B N).toRingHom) =>
          TrivSqZeroExt.snd
            ((LinearEquiv.ofBijective
              (Ideal.toCotangent (RingHom.ker (fstHom A B N).toRingHom))
              ⟨sorry, sorry⟩).symm x).1
        map_add' := sorry
        map_smul' := sorry }
      ⟨sorry, sorry⟩)

/-- The carrier of the split extension is `TrivSqZeroExt B N`. -/
theorem triv_carrier :
    (triv : SquareZeroAlgExtension A B N).carrier = TrivSqZeroExt B N := sorry

/-- The classifying cotangent map of a geometric representative. -/
def toHom (e : SquareZeroAlgExtension A B N) :
    (Generators.self A B).toExtension.Cotangent →ₗ[B] N :=
  -- Local instance justification (proof-local temporary data): unpack bundled `commRing` so evaluation of the self-presentation can elaborate.
  letI := e.commRing
  -- Local instance justification (proof-local temporary data): unpack bundled `algebra` so `MvPolynomial.aeval` can elaborate.
  letI := e.algebra
  -- Local instance justification (proof-local temporary data): unpack bundled `isSquareZero` so a set-theoretic section of `toB` exists.
  letI := e.isSquareZero
  { toFun := fun x =>
      let liftGen : B → e.carrier := Function.surjInv e.isSquareZero.surjective
      let φ : (Generators.self A B).toExtension.Ring →ₐ[A] e.carrier :=
        MvPolynomial.aeval liftGen
      let y := Function.surjInv Cotangent.mk_surjective x
      e.kernelEquiv (Ideal.toCotangent _ ⟨φ y.1, sorry⟩)
    map_add' := sorry
    map_smul' := sorry }

/-- The Ext¹ class of a geometric representative. -/
def toClass (e : SquareZeroAlgExtension A B N) : Exal A B N :=
  Exal.mk A B N (toHom e)

/-- `toClass` is the class of `toHom`. -/
theorem toClass_eq_mk (e : SquareZeroAlgExtension A B N) :
    toClass e = Exal.mk A B N (toHom e) := sorry

/-- Graph relations of a cotangent map in `TrivSqZeroExt` of the self-presentation ring. -/
def ofHomGraph (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    Set (TrivSqZeroExt (Generators.self A B).toExtension.Ring N) :=
  Set.range fun x : (Generators.self A B).toExtension.ker ↦
    (inl x.1 : TrivSqZeroExt (Generators.self A B).toExtension.Ring N) -
      inr (f (Cotangent.mk x))

/-- Unfolding of `ofHomGraph`. -/
theorem mem_ofHomGraph (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N)
    (z : TrivSqZeroExt (Generators.self A B).toExtension.Ring N) :
    z ∈ ofHomGraph f ↔
      ∃ x : (Generators.self A B).toExtension.ker,
        z = inl x.1 - inr (f (Cotangent.mk x)) := sorry

/-- The standard pushout square-zero extension attached to a cotangent map. -/
def ofHom (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    SquareZeroAlgExtension A B N :=
  let P := (Generators.self A B).toExtension
  -- Local instance justification (proof-local temporary data): restrict scalars along `P.Ring → B` so `N` is a `P.Ring`-module.
  letI := moduleRestrictScalars P.Ring B N
  -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `Module P.Ringᵐᵒᵖ N`; a global opposite-module instance on raw types diamonds.
  letI := moduleMulOpposite P.Ring N
  -- Local instance justification (instance diamond): `TrivSqZeroExt.commRing` needs `IsCentralScalar`; a global centrality instance on raw types diamonds.
  letI := isCentralScalar_of_commRing P.Ring N
  -- Local instance justification (proof-local temporary data): restrict scalars along `A → P.Ring` so `TrivSqZeroExt.algebra'` can elaborate.
  letI := moduleRestrictScalars A P.Ring N
  -- Local instance justification (proof-local temporary data): scalar tower for `TrivSqZeroExt.algebra'` along `A → P.Ring`.
  letI : IsScalarTower A P.Ring N := ⟨fun _ _ _ ↦ sorry⟩
  -- Local instance justification (proof-local temporary data): opposite scalar tower for `TrivSqZeroExt.algebra'`.
  letI : IsScalarTower A P.Ringᵐᵒᵖ N := ⟨fun _ _ _ ↦ sorry⟩
  -- Local instance justification (instance diamond): `SMulCommClass` for the opposite action used by `TrivSqZeroExt.algebra'`.
  letI : SMulCommClass P.Ring P.Ringᵐᵒᵖ N := ⟨fun _ _ _ ↦ sorry⟩
  let I := Ideal.span (ofHomGraph f)
  let toBRing :=
    Ideal.Quotient.lift I
      ((IsScalarTower.toAlgHom A P.Ring B).comp (fstHom A P.Ring N)).toRingHom
      (fun _ _ ↦ sorry)
  let toB : (TrivSqZeroExt P.Ring N ⧸ I) →ₐ[A] B :=
    { toRingHom := toBRing, commutes' := sorry }
  -- Local instance justification (proof-local temporary data): the pushout projection is square-zero, needed to assemble `of`.
  letI : toB.toRingHom.IsSquareZeroExtension := ⟨sorry, sorry⟩
  of toB
    (LinearEquiv.ofBijective
      { toFun := fun x : Ideal.Cotangent (RingHom.ker toB.toRingHom) ↦
          let y := (LinearEquiv.ofBijective (Ideal.toCotangent (RingHom.ker toB.toRingHom))
            ⟨sorry, sorry⟩).symm x
          Quotient.liftOn y.1
            (fun z ↦ TrivSqZeroExt.snd z +
              f (Cotangent.mk ⟨TrivSqZeroExt.fst z, sorry⟩))
            (fun _ _ _ ↦ sorry)
        map_add' := sorry
        map_smul' := sorry }
      ⟨sorry, sorry⟩)

/-- The Ext¹ class of the standard pushout extension is the class of the cotangent map. -/
theorem toClass_ofHom (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    toClass (ofHom f) = Exal.mk A B N f := sorry

end SquareZeroAlgExtension

end Algebra
