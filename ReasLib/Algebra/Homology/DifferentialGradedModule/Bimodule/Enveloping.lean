/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule

/-!
# Bimodules as Modules over an Enveloping DGA

The canonical model of differential graded bimodules makes the enveloping-algebra
classification definitional, while retaining a named equivalence for categorical downstream use.
-/

@[expose] public section

noncomputable section

universe u v w x

open CategoryTheory

namespace DifferentialGradedBimodule

variable {R : Type u} [CommRing R]

/-- Lemma 22.28.3 (0FQJ): differential graded `(A, B)`-bimodules are canonically equivalent
to right differential graded modules over `A.opposite ⊗[R] B`, allowing independent carrier
universes for the two DGAs. -/
@[stacks 0FQJ "differential graded bimodules over the enveloping algebra"]
def envelopingEquivalence
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) :
    DifferentialGradedBimodule A B ≌
      DifferentialGradedModule.{u, v} (CochainDGAlgebra.enveloping A B) :=
  CategoryTheory.Equivalence.refl

end DifferentialGradedBimodule
