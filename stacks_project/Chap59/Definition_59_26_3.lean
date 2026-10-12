/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.StandardEtale
import StacksCheckRecall

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S]

/- Definition 59.26.3: a commutative ring map `R →+* S` is standard étale if
`S` is isomorphic as an `R`-algebra to the principal localization at `g` of
`R[t]/(f)`, where `f, g ∈ R[t]`, `f` is monic, and its derivative is invertible
in `S`. The algebra structure on `S` is induced by the supplied ring map. -/
@[stacks 03PD] #check (RingHom.IsStandardEtale (R := R) (S := S) : (R →+* S) → Prop)
