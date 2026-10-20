module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.RationalCurve
import StacksCheckRecall

/-!
# No rational curves on group algebraic spaces

A separated group algebraic space locally of finite type over a field admits
no nonconstant morphism from the projective line over that field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 79.11.3: Let `k` be a field. Let `G` be a separated group algebraic
space locally of finite type over `k`. Every morphism from the projective line
over `k` to `G` over `Spec k` is constant. -/
@[stacks 0AEN]
#check (AlgebraicGeometry.GroupAlgebraicSpace.isConstant_hom_projectiveLine :
  ∀ {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (SchemeRealization.toBase G.X.left)]
    (f : ofOver (ProjectiveSpace.schemeOver k 1) ⟶ G.X.left),
    AlgebraicSpace.IsConstant f)
