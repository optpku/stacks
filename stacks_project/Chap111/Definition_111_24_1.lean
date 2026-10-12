/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.GoingUpDown
import StacksCheckRecall

@[expose] public section

/-!
# Definition 111.24.1

@stack 027U
-/

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)

/- Definition 111.24.1 (1): a ring map `φ : R →+* S` satisfies going up exactly when the induced
map `Spec(S) → Spec(R)` is a specializing map. -/
@[stacks 027U "(1)"]
#check (RingHom.HasGoingUp φ : Prop)

/- Definition 111.24.1 (2): after installing the canonical algebra structure from `φ`, the
going-down property is the owner predicate `Algebra.HasGoingDown R S`. -/
@[stacks 027U "(2)"]
#check (RingHom.HasGoingDown φ : Prop)

end
