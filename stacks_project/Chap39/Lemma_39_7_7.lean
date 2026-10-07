module

public import ReasLib.AlgebraicGeometry.GroupScheme.Topology
import StacksCheckRecall

universe u

/- Lemma 39.7.7: Let `ψ : G' ⟶ G` be a morphism of group schemes over a field. If the
pointwise range of `ψ` is open in `G`, then it is closed in `G`. -/
@[stacks 047S] #check
  (AlgebraicGeometry.GroupScheme.isClosed_range_of_isOpen :
    ∀ {k : Type u} [Field k]
      {G' G : AlgebraicGeometry.SchemeOverField k}
      [CategoryTheory.GrpObj G'] [CategoryTheory.GrpObj G]
      (ψ : G' ⟶ G) [CategoryTheory.IsMonHom ψ],
      IsOpen (Set.range ψ.left.base) → IsClosed (Set.range ψ.left.base))
