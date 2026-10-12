/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Surjective Ring Pullback Situations

A surjective ring pullback situation consists of maps `B → A` and `A' → A`, with the latter
surjective. Its derived ring and projections are the canonical pullback in `CommRingCat`.

@stack 08KH
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

universe u

noncomputable section

/-- Two ring maps `B → A` and `A' → A`, with `A' → A` surjective, whose canonical
pullback is the fiber-product ring `B ×_A A'`. -/
@[stacks 08KH]
structure SurjectiveRingPullbackSituation
    (B A A' : Type u) [CommRing B] [CommRing A] [CommRing A'] where
  /-- The ring map `B → A`. -/
  toA : B →+* A
  /-- The ring map `A' → A`. -/
  fromAprime : A' →+* A
  /-- The map `A' → A` is surjective. -/
  fromAprime_surjective : Function.Surjective fromAprime

namespace SurjectiveRingPullbackSituation

variable {B A A' : Type u} [CommRing B] [CommRing A] [CommRing A']

/-- Construct a surjective ring pullback situation from two ring maps and surjectivity of the
second map. -/
def ofSurjective (toA : B →+* A) (fromAprime : A' →+* A)
    (fromAprime_surjective : Function.Surjective fromAprime) :
    SurjectiveRingPullbackSituation B A A' where
  toA := toA
  fromAprime := fromAprime
  fromAprime_surjective := fromAprime_surjective

variable (S : SurjectiveRingPullbackSituation B A A')

/-- The canonical fiber-product ring `B' = B ×_A A'`. -/
@[stacks 08KH "surjective pullback ring"]
abbrev Bprime : CommRingCat :=
  pullback (ofHom S.toA) (ofHom S.fromAprime)

/-- The canonical projection `B' → B`. -/
@[stacks 08KH "first surjective pullback projection"]
abbrev bprimeToB : S.Bprime →+* B :=
  (pullback.fst (ofHom S.toA) (ofHom S.fromAprime)).hom

/-- The canonical projection `B' → A'`. -/
@[stacks 08KH "second surjective pullback projection"]
abbrev bprimeToAprime : S.Bprime →+* A' :=
  (pullback.snd (ofHom S.toA) (ofHom S.fromAprime)).hom

/-- The two pullback projections satisfy the defining commutativity relation. -/
@[stacks 08KH "pullback commutativity"]
theorem comm :
    S.toA.comp S.bprimeToB = S.fromAprime.comp S.bprimeToAprime := sorry

/-- The square defined by the fiber-product projections is a categorical pullback square. -/
@[stacks 08KH "pullback square"]
theorem isPullback :
    IsPullback (ofHom S.bprimeToB) (ofHom S.bprimeToAprime)
      (ofHom S.toA) (ofHom S.fromAprime) := sorry

end SurjectiveRingPullbackSituation
