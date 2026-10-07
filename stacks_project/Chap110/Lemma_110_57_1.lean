module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.DimensionCutoff
import StacksCheckRecall

/-!
# An étale abelian sheaf vanishing below a dimension cutoff
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

/- Lemma 110.57.1: there exists a sheaf of abelian groups `G` on the big
étale site such that `G(X) = 0` whenever `topologicalKrullDim X < n`,
`G(X)` is not zero whenever `n ≤ topologicalKrullDim X`, and restriction
along every thickening `X ⟶ X'` is an isomorphism. -/
@[stacks 05LE]
#check (AlgebraicGeometry.Scheme.exists_etaleSheaf_dimensionCutoff :
  ∀ n : ℕ,
    ∃ G : Sheaf Scheme.etaleTopology AddCommGrpCat.{u},
      (∀ X : Scheme.{u}, IsZero (G.obj.obj (op X)) ↔ topologicalKrullDim X < n) ∧
        (∀ {X Y : Scheme.{u}} (i : X ⟶ Y) [IsThickening i],
          IsIso (G.obj.map i.op)))
