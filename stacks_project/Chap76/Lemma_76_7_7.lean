module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Differentials.Composition
import StacksCheckRecall

/-!
# Functoriality of differential comparisons for morphisms of algebraic spaces

A commutative ladder of algebraic spaces over a scheme `S` induces the composition law
`c_{f ∘ g} = c_g ∘ g^* c_f` on the comparison morphisms of relative differentials.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

noncomputable section

universe u

/- Lemma 76.7.7: for a commutative diagram of algebraic spaces over a scheme `S`, the
differential comparisons satisfy `c_{f ∘ g} = c_g ∘ g^* c_f` as maps
`(g ≫ f)^* (relativeDifferentials h) ⟶ relativeDifferentials h''`. -/
@[stacks 05Z7] #check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.comparison_comp :
  ∀ {S : Scheme.{u}} {X X' X'' Y Y' Y'' : AlgebraicSpace S}
    (f : X' ⟶ X) (g : X'' ⟶ X') (u : Y' ⟶ Y) (v : Y'' ⟶ Y')
    (h : X ⟶ Y) (h' : X' ⟶ Y') (h'' : X'' ⟶ Y'')
    (sq : CommSq f h' h u) (sq' : CommSq g h'' h' v),
  comparison (g ≫ f) (v ≫ u) h h'' (CommSq.horiz_comp sq' sq).w =
    comparisonComp f g u v h h' h'' sq sq')

/- The reusable owner supplies the concrete composite `c_g ∘ g^* c_f` after identifying
`(g ≫ f)^*` with `g^* ∘ f^*`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.Differentials.comparisonComp :
  ∀ {S : Scheme.{u}} {X X' X'' Y Y' Y'' : AlgebraicSpace S}
    (f : X' ⟶ X) (g : X'' ⟶ X') (u : Y' ⟶ Y) (v : Y'' ⟶ Y')
    (h : X ⟶ Y) (h' : X' ⟶ Y') (h'' : X'' ⟶ Y'')
    (sq : CommSq f h' h u) (sq' : CommSq g h'' h' v),
  (Modules.pullback (g ≫ f)).obj (relativeDifferentials h) ⟶ relativeDifferentials h'')

