module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Graph of a morphism of algebraic stacks over a base

A 1-morphism `g : X ⟶ Y` of groupoid fibrations over `T`, together with a
2-isomorphism `g ≫ y ≅ x`, determines a pseudo-pullback cone with legs `𝟙 X`
and `g`. Its universal lift into `TwoFibreProduct.apex x y` is the graph
`X ⟶ X ×_T Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The pairing of the identity of `X` with `g : X ⟶ Y` as a pseudo-pullback
cone over the structure morphisms `x : X ⟶ T` and `y : Y ⟶ T`, using the given
2-isomorphism `hg : g ≫ y ≅ x`. -/
def graphCone {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) :
    PseudoPullbackCone x y where
  pt := X
  fst := 𝟙 X
  snd := g
  iso := λ_ x ≪≫ hg.symm

/-- The graph 1-morphism `X ⟶ TwoFibreProduct.apex x y` of `g` over `T`,
obtained as the universal lift of `graphCone x y g hg` into the two-fibre
product of `x` and `y`. -/
def graph {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) :
    X ⟶ TwoFibreProduct.apex.{u + 1, u, u + 1, u} x y :=
  PseudoPullbackCone.lift (graphCone x y g hg)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x y)

/-- `graph x y g hg` is the universal lift of `graphCone x y g hg` into the
two-fibre product of `x` and `y`. -/
theorem graph_eq {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) :
    graph x y g hg =
      PseudoPullbackCone.lift (graphCone x y g hg)
        (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x y) :=
  sorry

/-- The first projection of the graph of `g` is isomorphic to the identity of
`X`. -/
def graph_fst {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) :
    graph x y g hg ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} x y ≅ 𝟙 X :=
  PseudoPullbackCone.lift.fstIso (graphCone x y g hg)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x y)

/-- The second projection of the graph of `g` is isomorphic to `g`. -/
def graph_snd {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) :
    graph x y g hg ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} x y ≅ g :=
  PseudoPullbackCone.lift.sndIso (graphCone x y g hg)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} x y)

end AlgebraicGeometry.AlgebraicStack
