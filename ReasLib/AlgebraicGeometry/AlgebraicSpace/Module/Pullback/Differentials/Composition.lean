module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials

/-!
# Composition of differential comparisons for algebraic spaces

The comparison attached to a pasted pair of commutative squares of algebraic spaces is the
composite of the two individual comparisons after the canonical identification of pullback along
a composite with iterated pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

variable {S : Scheme.{u}}
variable {X X' X'' Y Y' Y'' : AlgebraicSpace S}
variable (f : X' ⟶ X) (g : X'' ⟶ X') (u : Y' ⟶ Y) (v : Y'' ⟶ Y')
variable (h : X ⟶ Y) (h' : X' ⟶ Y') (h'' : X'' ⟶ Y'')
variable (sq : CommSq f h' h u) (sq' : CommSq g h'' h' v)

/-- The iterated comparison associated to two composable commutative squares of algebraic
spaces, transported along the identification of pullback along a composite with iterated
pullback. -/
def comparisonComp :
    (Modules.pullback (g ≫ f)).obj (relativeDifferentials h) ⟶ relativeDifferentials h'' :=
  (Modules.pullbackCompIso g f).inv.app (relativeDifferentials h) ≫
    (Modules.pullback g).map (comparison f u h h' sq.w) ≫
    comparison g v h' h'' sq'.w

/-- Pullback comparison morphisms for relative differentials of algebraic spaces are compatible
with composition of commutative squares. -/
theorem comparison_comp :
    comparison (g ≫ f) (v ≫ u) h h'' (CommSq.horiz_comp sq' sq).w =
      comparisonComp f g u v h h' h'' sq sq' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
