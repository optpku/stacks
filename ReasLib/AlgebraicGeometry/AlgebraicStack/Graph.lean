module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

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
open FiberedCategoryOver.Groupoids
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
  rfl

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

namespace AlgebraicGeometry.Groupoids.Hom

namespace LocallyOfFiniteType

/-- The graph of a morphism of algebraic stacks over an algebraic stack is
representable by algebraic spaces and locally of finite type. -/
instance graph {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) :
    LocallyOfFiniteType (AlgebraicStack.graph x y g hg) :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.Groupoids.Hom

namespace AlgebraicGeometry.AlgebraicStack

/-- The graph `graph x y g hg` is representable by algebraic spaces. -/
theorem relativelyRepresentable_graph {S : Scheme.{u}}
    {X Y T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack T] (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y)
    (hg : g ≫ y ≅ x) :
    relativelyRepresentableByAlgebraicSpaces (graph x y g hg) :=
  Groupoids.Hom.LocallyOfFiniteType.representable
    (f := graph x y g hg)

/-- The graph of a morphism of algebraic stacks over a base is unramified
when the target structure morphism is DM. -/
theorem graph_unramified {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [DM y] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic stacks over a base is locally
quasi-finite when the target structure morphism is quasi-DM. -/
theorem graph_locallyQuasiFinite {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [QuasiDM y] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic stacks over a base is proper when
the target structure morphism is separated. -/
theorem graph_proper {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [Separated y] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (graph x y g hg) :=
  sorry

/-- The graph of a morphism of algebraic stacks over a base is quasi-compact
and quasi-separated when the target structure morphism is quasi-separated. -/
theorem graph_quasiCompact_quasiSeparated {S : Scheme.{u}}
    {X Y T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack T] (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y)
    (hg : g ≫ y ≅ x) [QuasiSeparated y] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (graph x y g hg) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (graph x y g hg) :=
  sorry

/-- The graph of a morphism over a quasi-separated morphism is quasi-compact. -/
theorem graph_quasiCompact {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x)
    [QuasiSeparated y] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (graph x y g hg) :=
  (graph_quasiCompact_quasiSeparated x y g hg).1

/-- The graph of a morphism over a quasi-separated morphism is
quasi-separated. -/
theorem graph_isQuasiSeparated {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x)
    [QuasiSeparated y] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (graph x y g hg) :=
  (graph_quasiCompact_quasiSeparated x y g hg).2

end AlgebraicGeometry.AlgebraicStack
