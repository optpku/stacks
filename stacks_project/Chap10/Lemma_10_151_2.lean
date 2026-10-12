/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Unramified.Basic
import StacksCheckRecall

/-! @stack 00UU -/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.151.2 (1): a ring map is unramified exactly when it is
formally unramified and of finite type. -/
@[stacks 00UU "(1)"]
#check (Unramified.iff_formallyUnramified_and_finiteType R S :
  Unramified R S ↔ FormallyUnramified R S ∧ FiniteType R S)

/- Lemma 10.151.2 (2): a ring map is G-unramified exactly when it is
formally unramified and of finite presentation. -/
@[stacks 00UU "(2)"]
#check (GUnramified.iff_formallyUnramified_and_finitePresentation R S :
  GUnramified R S ↔ FormallyUnramified R S ∧ FinitePresentation R S)

end Algebra
