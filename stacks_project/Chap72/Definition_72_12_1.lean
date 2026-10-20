module

public import stacks_project.Chap72.Lemma_72_14_3_Geometrically
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.12.1: An algebraic space over a field k is geometrically connected over k
if every base change along a field extension is connected. -/
@[stacks 0A0Z] #check (AlgebraicGeometry.AlgebraicSpace.GeometricallyConnected.iff :
  ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (of k))),
    GeometricallyConnected X ↔
      ∀ (K : Type u) [Field K] [Algebra k K],
        ConnectedSpace (Points (baseChange (Spec.map (ofHom (algebraMap k K))) X)))
