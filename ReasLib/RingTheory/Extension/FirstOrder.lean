/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.OfSurjective
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.Ideal.Quotient.ULift

/-!
# Universal First-Order Thickenings

This file owns the universal property of a first-order thickening of an algebra.
The predicate is explicitly universe-indexed: `IsUniversal.{x} P` tests
square-zero quotients whose carrier lies in `Type x`.  This makes universe
requirements visible without forcing callers to spell every implicit argument.

The conormal module is represented by Mathlib's canonical `Extension.Cotangent`.
For a square-zero extension, `Extension.kerCotangentEquiv` identifies the kernel
with that quotient without introducing a second carrier or a proof-indexed module
instance.

@stack 04EC
-/

@[expose] public section

noncomputable section

open Algebra

namespace Algebra.Extension

namespace FirstOrder

/-- An extension is universal among square-zero extensions of its target.

The leading universe parameter is the universe of the testing algebras. -/
@[stacks 04EC "universal first-order thickening"]
def IsUniversal.{x, u, v, w}
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : Prop :=
  P.ker ^ 2 = ⊥ ∧
    ∀ {A : Type x} [CommRing A] [Algebra R A]
      (I : Ideal A) (_ : I ^ 2 = ⊥) (f : S →ₐ[R] A ⧸ I),
        ∃! g : P.Ring →ₐ[R] A,
          (Ideal.Quotient.mkₐ R I).comp g =
            f.comp (IsScalarTower.toAlgHom R P.Ring S)

universe u v w x y

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

namespace IsUniversal

variable {P : Extension.{w} R S}

/-- The kernel of a universal first-order thickening has square zero. -/
@[stacks 04EC "square-zero kernel"]
theorem squareZero (hP : IsUniversal.{x} P) : P.ker ^ 2 = ⊥ :=
  hP.1

/-- The lifting property when the test algebra is already in the predicate's universe. -/
@[stacks 04EC "unique lift in the testing universe"]
theorem existsUniqueLiftAt
    (hP : IsUniversal.{x} P)
    {A : Type x} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) (f : S →ₐ[R] A ⧸ I) :
    ∃! g : P.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp g =
        f.comp (IsScalarTower.toAlgHom R P.Ring S) :=
  hP.2 I hI f

/-- The lifting property for a test algebra in a lower universe.

The `max x y` in the hypothesis is essential: `ULift` can raise `A : Type x`
to the predicate's testing universe, but cannot shrink an arbitrary larger
algebra into a fixed smaller universe. -/
@[stacks 04EC "unique lift after universe lifting"]
theorem existsUniqueLift
    (hP : IsUniversal.{max x y} P)
    {A : Type x} [CommRing A] [Algebra R A]
    (I : Ideal A) (hI : I ^ 2 = ⊥) (f : S →ₐ[R] A ⧸ I) :
    ∃! g : P.Ring →ₐ[R] A,
      (Ideal.Quotient.mkₐ R I).comp g =
        f.comp (IsScalarTower.toAlgHom R P.Ring S) := by
  let I' : Ideal (ULift.{y} A) := I.map (algebraMap A (ULift.{y} A))
  have hI' : I' ^ 2 = ⊥ := by
    dsimp [I']
    rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let e : (ULift.{y} A ⧸ I') ≃ₐ[R] A ⧸ I :=
    Ideal.uliftQuotientAlgEquiv (R := R) I
  let f' : S →ₐ[R] ULift.{y} A ⧸ I' := e.symm.toAlgHom.comp f
  obtain ⟨g', hg', huniq'⟩ := hP.existsUniqueLiftAt I' hI' f'
  let d : ULift.{y} A ≃ₐ[R] A := ULift.algEquiv
  let g : P.Ring →ₐ[R] A := d.toAlgHom.comp g'
  refine ⟨g, ?_, ?_⟩
  · apply AlgHom.ext
    intro p
    have hp := congrArg e (DFunLike.congr_fun hg' p)
    simpa [g, d, f', e, I', AlgHom.comp_apply] using hp
  · intro q hq
    let q' : P.Ring →ₐ[R] ULift.{y} A := d.symm.toAlgHom.comp q
    have hq' :
        (Ideal.Quotient.mkₐ R I').comp q' =
          f'.comp (IsScalarTower.toAlgHom R P.Ring S) := by
      apply AlgHom.ext
      intro p
      apply e.injective
      have hp := DFunLike.congr_fun hq p
      simpa [q', d, f', e, I', AlgHom.comp_apply] using hp
    have hqg := huniq' q' hq'
    apply AlgHom.ext
    intro p
    have hp := DFunLike.congr_fun hqg p
    simpa [g, q', d, AlgHom.comp_apply] using congrArg d hp

end IsUniversal

end FirstOrder

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- For a square-zero extension, the kernel is canonically equivalent to its
cotangent module `ker(P → S) / ker(P → S)²`. -/
@[stacks 04EC "conormal module of a square-zero extension"]
noncomputable def kerCotangentEquiv (P : Extension.{w} R S)
    (hsq : P.ker ^ 2 = ⊥) : P.ker ≃ₗ[P.Ring] P.Cotangent := by
  refine LinearEquiv.ofBijective Extension.Cotangent.mk ⟨?_, Extension.Cotangent.mk_surjective⟩
  intro a b hab
  apply Subtype.ext
  apply sub_eq_zero.mp
  simpa [hsq, Ideal.mem_bot] using
    (Extension.Cotangent.mk_eq_mk_iff_sub_mem a b).mp hab

@[simp]
theorem kerCotangentEquiv_apply (P : Extension.{w} R S)
    (hsq : P.ker ^ 2 = ⊥) (x : P.ker) :
    P.kerCotangentEquiv hsq x = Extension.Cotangent.mk x :=
  rfl

@[simp]
theorem kerCotangentEquiv_symm_mk (P : Extension.{w} R S)
    (hsq : P.ker ^ 2 = ⊥) (x : P.ker) :
    (P.kerCotangentEquiv hsq).symm (Extension.Cotangent.mk x) = x :=
  (P.kerCotangentEquiv hsq).symm_apply_apply x

end Algebra.Extension
