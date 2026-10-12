/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Kaehler.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.131.2

@stack 07BK
-/

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Definition 10.131.2: the module of Kähler differentials of the `R`-algebra `S`, together with
its universal derivation `d`, is the canonical pair consisting of `Ω[S⁄R]` and
`KaehlerDifferential.D R S`. -/
@[stacks 07BK]
#check (KaehlerDifferential.D R S : Derivation R S Ω[S⁄R])
