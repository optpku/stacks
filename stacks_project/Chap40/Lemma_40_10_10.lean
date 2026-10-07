module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Dimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

/- Lemma 40.10.10: If the object scheme of a groupoid scheme is the spectrum of a field
and its source and target maps are locally of finite type, then its arrow scheme and its
stabilizer have equal topological Krull dimension. -/
@[stacks 04MQ] #check
  (AlgebraicGeometry.GroupoidScheme.topologicalKrullDim_arrow_eq_stabilizer :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S)
      {k : Type u} [Field k]
      (uIso : G.U.left ≅ AlgebraicGeometry.Spec (CommRingCat.of k))
      [AlgebraicGeometry.LocallyOfFiniteType G.s.left]
      [AlgebraicGeometry.LocallyOfFiniteType G.t.left],
    topologicalKrullDim G.R.left =
      topologicalKrullDim G.stabilizer.X.left.left)
