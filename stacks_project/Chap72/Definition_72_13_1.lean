module

public import stacks_project.Chap72.Lemma_72_14_3_Geometrically
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.13.1: A decent algebraic space X over a field k is geometrically
irreducible if |X_{k'}| is irreducible after every field extension k'/k.
Irreducible spaces are nonempty by convention. -/
@[stacks 0DMU] #check
  (fun {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [IsDecent X] ↦
    AlgebraicGeometry.AlgebraicSpace.GeometricallyIrreducible.iff X :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))) [IsDecent X],
      GeometricallyIrreducible X ↔
        ∀ (K : Type u) [Field K] [Algebra k K],
          IrreducibleSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))
