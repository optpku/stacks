/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring-hom finite presentation from algebra finiteness

This leaf records the restriction-of-scalars bridge that is often needed when
an argument is stated with an `R`-algebra map but a downstream localization
criterion consumes the underlying map as a homomorphism of rings.
-/

@[expose] public section

universe u v w

namespace RingHom.FinitePresentation

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]

/-- Tag `087P`: if the source algebra is finite type over `R` and the target
algebra is finite presentation over `R`, every `R`-algebra map between them is
finite presentation as a ring homomorphism.  This is the reusable
restriction-of-scalars bridge; the localization criteria themselves can keep
the smaller direct input `RingHom.FinitePresentation f`. -/
@[stacks 087P "finite presentation of an algebra map after restriction of scalars"]
theorem of_algebra (f : S →ₐ[R] T)
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R T] :
    RingHom.FinitePresentation (f : S →+* T) := sorry

end RingHom.FinitePresentation
