module

public import ReasLib.AlgebraicGeometry.GroupScheme.Counterexamples
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 110.49.1: there exists a group scheme `G` over a base `S` whose
identity component is flat over `S` but which is not flat over `S`. -/
@[stacks 06RK] #check (AlgebraicGeometry.GroupScheme.exists_identityComponent_flat_not_flat :
    ∃ (S : Scheme.{u}) (G : GroupScheme S) (hopen : IsOpen
      (AlgebraicGeometry.GroupScheme.identityComponentLocus G)),
      AlgebraicGeometry.Flat
          (Scheme.Opens.ι
            ⟨AlgebraicGeometry.GroupScheme.identityComponentLocus G, hopen⟩ ≫ G.X.hom) ∧
        ¬ AlgebraicGeometry.Flat G.X.hom)
