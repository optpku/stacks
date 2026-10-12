/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Locally Nilpotent Ideals

This module owns the predicate that every element of an ideal is nilpotent.  Its canonical
order-theoretic form is containment in the nilradical, while the elementwise characterization is
provided as the primary computation API.
-/

universe u v

namespace Ideal

section

variable {R : Type u} [CommSemiring R]

/-- An ideal is locally nilpotent when all of its elements are nilpotent; equivalently, it is
contained in the nilradical. -/
@[stacks 00IL]
abbrev IsLocallyNilpotent (I : Ideal R) : Prop :=
  I ≤ nilradical R

/-- The order-theoretic formulation of a locally nilpotent ideal is containment in the
nilradical. -/
@[stacks 00IL "locally nilpotent ideal as nilradical containment"]
theorem isLocallyNilpotent_iff_le_nilradical (I : Ideal R) :
    I.IsLocallyNilpotent ↔ I ≤ nilradical R :=
  Iff.rfl

/-- An ideal is locally nilpotent exactly when every one of its elements is nilpotent. This is an
explicit computation lemma rather than a global simp rule, so nilradical-containment goals remain
available for order-theoretic composition. -/
@[stacks 00IL "elementwise locally nilpotent ideal criterion"]
theorem isLocallyNilpotent_iff (I : Ideal R) :
    I.IsLocallyNilpotent ↔ ∀ x ∈ I, IsNilpotent x := by
  simp only [IsLocallyNilpotent, SetLike.le_def, mem_nilradical]

/-- A subideal of a locally nilpotent ideal is locally nilpotent. -/
@[stacks 00IL "local nilpotence is downward closed"]
theorem isLocallyNilpotent_of_le {I J : Ideal R} (hJI : J ≤ I)
    (hI : I.IsLocallyNilpotent) : J.IsLocallyNilpotent :=
  hJI.trans hI

namespace FG

/-- A finitely generated subideal of a locally nilpotent ideal is nilpotent.

This is the reusable bridge from elementwise nilpotence to nilpotence of an ideal; callers should
provide the containment rather than unfold `IsLocallyNilpotent` to its nilradical formulation. -/
@[stacks 00IL "finitely generated locally nilpotent subideal"]
theorem isNilpotent_of_le_locallyNilpotent
    {I J : Ideal R} (hJfg : J.FG) (hJI : J ≤ I)
    (hI : I.IsLocallyNilpotent) : IsNilpotent J :=
  (hJfg.isNilpotent_iff_le_nilradical).2 (hJI.trans hI)

end FG

end

namespace IsLocallyNilpotent

section

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]

/-- A locally nilpotent ideal is contained in every prime ideal. -/
@[stacks 00IL "locally nilpotent ideals lie in every prime"]
theorem le_prime {I : Ideal R} (hI : I.IsLocallyNilpotent)
    (p : Ideal R) [p.IsPrime] : I ≤ p :=
  hI.trans (nilradical_le_prime p)

/-- The image of a locally nilpotent ideal under a ring homomorphism is locally nilpotent. -/
@[stacks 00IL "image of a locally nilpotent ideal"]
theorem map {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : R →+* S) :
    (I.map f).IsLocallyNilpotent := by
  rw [isLocallyNilpotent_iff_le_nilradical, Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_nilradical]
  exact (mem_nilradical.mp (hI hx)).map f

/-- The preimage of a locally nilpotent ideal is locally nilpotent when the
kernel of the ring map is locally nilpotent. -/
@[stacks 00IL "preimage of a locally nilpotent ideal"]
theorem comap {I : Ideal S} (hI : I.IsLocallyNilpotent) (f : R →+* S)
    (hker : (RingHom.ker f).IsLocallyNilpotent) :
    (I.comap f).IsLocallyNilpotent := by
  rw [isLocallyNilpotent_iff] at hI hker ⊢
  intro x hx
  obtain ⟨n, hn⟩ := hI (f x) hx
  have hxpow : x ^ n ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_pow, hn]
  obtain ⟨m, hm⟩ := hker (x ^ n) hxpow
  exact ⟨n * m, by rwa [pow_mul]⟩

end

end IsLocallyNilpotent

end Ideal
