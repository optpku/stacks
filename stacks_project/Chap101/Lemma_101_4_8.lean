/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Lemma_100_11_2_LocallyOfFiniteType
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap101.Lemma_101_4_8_Graph

/-!
# Graph of a morphism of algebraic stacks over a base

For a morphism `g : X ⟶ Y` of algebraic stacks over an algebraic stack `T`,
the graph `graph x y g hg : X ⟶ X ×_T Y` is representable by algebraic spaces
and locally of finite type. It is unramified if `Y ⟶ T` is DM, locally
quasi-finite if `Y ⟶ T` is quasi-DM, proper if `Y ⟶ T` is separated, and
quasi-compact and quasi-separated if `Y ⟶ T` is quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace LocallyOfFiniteType

/-- Lemma 101.4.8 (1): let `T` be an algebraic stack and let `g : X ⟶ Y` be a
morphism of algebraic stacks over `T`. The graph
`graph x y g hg : X ⟶ X ×_T Y` is representable by algebraic spaces and
locally of finite type. -/
@[stacks 050I]
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
  sorry

/-- Lemma 101.4.8 (2): let `T` be an algebraic stack and let `g : X ⟶ Y` be a
morphism of algebraic stacks over `T`. If `Y ⟶ T` is DM, then the graph
`graph x y g hg` is unramified. -/
@[stacks 050I]
theorem graph_unramified {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [DM y] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (graph x y g hg) :=
  sorry

/-- Lemma 101.4.8 (3): let `T` be an algebraic stack and let `g : X ⟶ Y` be a
morphism of algebraic stacks over `T`. If `Y ⟶ T` is quasi-DM, then the graph
`graph x y g hg` is locally quasi-finite. -/
@[stacks 050I]
theorem graph_locallyQuasiFinite {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [QuasiDM y] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (graph x y g hg) :=
  sorry

/-- Lemma 101.4.8 (4): let `T` be an algebraic stack and let `g : X ⟶ Y` be a
morphism of algebraic stacks over `T`. If `Y ⟶ T` is separated, then the graph
`graph x y g hg` is proper. -/
@[stacks 050I]
theorem graph_proper {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [Separated y] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (graph x y g hg) :=
  sorry

/-- Lemma 101.4.8 (5): let `T` be an algebraic stack and let `g : X ⟶ Y` be a
morphism of algebraic stacks over `T`. If `Y ⟶ T` is quasi-separated, then the
graph `graph x y g hg` is quasi-compact and quasi-separated. -/
@[stacks 050I]
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
  sorry

/-- The graph of a morphism over a quasi-separated morphism is
quasi-separated. -/
theorem graph_isQuasiSeparated {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x)
    [QuasiSeparated y] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (graph x y g hg) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
