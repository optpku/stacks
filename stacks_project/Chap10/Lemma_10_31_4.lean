/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.31.4

@stack 00FP
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section Modules

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

/- Lemma 10.31.4 (1): over a Noetherian ring, every finite `R`-module is finitely presented.
This is exactly the canonical theorem `Module.finitePresentation_of_finite`. -/
@[stacks 00FP "finite module is finitely presented"]
#check @Module.finitePresentation_of_finite

variable (N : Submodule R M)

/- Lemma 10.31.4 (2): any submodule of a finite `R`-module is finite over a Noetherian ring.
The owner theorem is `isNoetherian_of_submodule_of_noetherian`; the source-facing finiteness
statement is its derived canonical instance consequence. -/
@[stacks 00FP "submodule finiteness"]
#check @isNoetherian_of_submodule_of_noetherian
@[stacks 00FP "finite submodule consequence"]
#check (inferInstance : Module.Finite R N)

end Modules

section Algebras

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [IsNoetherianRing R] [Algebra.FiniteType R A]

/- Lemma 10.31.4 (3): over a Noetherian ring, any finite type `R`-algebra is finitely presented
over `R`. This is the forward direction of the canonical theorem
`Algebra.FinitePresentation.of_finiteType`. -/
@[stacks 00FP "finite type algebra is finitely presented"]
#check @Algebra.FinitePresentation.of_finiteType

end Algebras
