/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.TorDimension.Presentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 23.7.3

The reusable statement is map-first and uses mathlib's bundled
`Algebra.Presentation`; this chapter file records the source label only.
-/

/- Lemma 23.7.3 (Tag 09PU): a nonnilpotent obstruction associated to a
relation lifted across a principal square-zero extension rules out finite Tor
dimension of the presented algebra. -/
universe u' u v w t

section

variable {R' : Type u'} {R : Type u} {S : Type v}
variable [CommRing R'] [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R'] [IsNoetherianRing R]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {g : RingHom.SquareZeroExtension.Generator f}
variable {ι : Type w} {σ : Type t} [Fintype σ]
variable {P : Algebra.Presentation R S ι σ}
variable (L : Algebra.Presentation.LiftedRelation g P)
variable (hL : ¬ IsNilpotent L.obstruction)

@[stacks 09PU]
#check (Algebra.Presentation.LiftedRelation.not_hasFiniteTorDimension L hL :
  ¬ (algebraMap R S).HasFiniteTorDimension)

end

#check @Algebra.Presentation.LiftedRelation.obstruction
#check @Algebra.Presentation.LiftedRelation.not_isPerfectRingMap
