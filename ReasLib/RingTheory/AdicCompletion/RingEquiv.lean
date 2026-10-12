/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Adic completion transport along ring equivalences

This file constructs the comparison equivalence between adic completions when
a ring equivalence identifies the defining ideals.
-/

@[expose] public section

noncomputable section

universe u v

namespace AdicCompletion

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Finite-stage comparison maps of adic completions along a ring
equivalence that identifies the defining ideals. -/
def ringCongrFamily (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) (n : ℕ) :
    AdicCompletion I R →+* S ⧸ J ^ n :=
  (Ideal.quotientEquiv (I ^ n) (J ^ n) e
      ((Ideal.map_pow e.toRingHom I n).trans (congrArg (fun K => K ^ n) h)).symm).toRingHom.comp
    (evalₐ I n).toRingHom

/-- The finite-stage comparison maps commute with the inverse-system
transition maps. -/
theorem ringCongrFamily_compatible (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (ringCongrFamily e h n) =
      ringCongrFamily e h m := sorry

/-- The ring homomorphism of adic completions induced by a ring
equivalence identifying the defining ideals. -/
def ringCongrHom (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) :
    AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J (ringCongrFamily e h) (ringCongrFamily_compatible e h)

/-- The comparison homomorphisms along a ring equivalence and its inverse
compose to the identity on the codomain completion. -/
theorem ringCongrHom_comp (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) :
    (ringCongrHom e h).comp (ringCongrHom e.symm (h ▸ Ideal.map_of_equiv e)) =
      RingHom.id (AdicCompletion J S) := sorry

/-- The comparison homomorphisms along a ring equivalence and its inverse
compose to the identity on the domain completion. -/
theorem ringCongrHom_symm_comp (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) :
    (ringCongrHom e.symm (h ▸ Ideal.map_of_equiv e)).comp (ringCongrHom e h) =
      RingHom.id (AdicCompletion I R) := sorry

/-- A ring equivalence sending `I` to `J` identifies the corresponding
adic completions. -/
def ringCongr (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) :
    AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (ringCongrHom e h)
    (ringCongrHom e.symm (h ▸ Ideal.map_of_equiv e))
    (ringCongrHom_comp e h) (ringCongrHom_symm_comp e h)

/-- The comparison of completions preserves the canonical image of the
original ring. -/
theorem ringCongr_of (e : R ≃+* S) {I : Ideal R} {J : Ideal S}
    (h : I.map e.toRingHom = J) (x : R) :
    ringCongr e h (of I R x) = of J S (e x) := sorry

end AdicCompletion
