/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Graph
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.4.8: the graph of a morphism of algebraic stacks over an algebraic
stack is representable by algebraic spaces and locally of finite type. It is
unramified over a DM morphism, locally quasi-finite over a quasi-DM morphism,
proper over a separated morphism, and quasi-compact and quasi-separated over
a quasi-separated morphism. -/
@[stacks 050I] #check (AlgebraicGeometry.Groupoids.Hom.LocallyOfFiniteType.graph :
    ∀ {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x),
    Groupoids.Hom.LocallyOfFiniteType (AlgebraicStack.graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.relativelyRepresentable_graph :
    ∀ {S : Scheme.{u}}
    {X Y T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack T] (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y)
    (hg : g ≫ y ≅ x),
    relativelyRepresentableByAlgebraicSpaces (graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.graph_unramified :
    ∀ {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [DM y],
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S) (graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.graph_locallyQuasiFinite :
    ∀ {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [QuasiDM y],
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) (graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.graph_proper :
    ∀ {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x) [Separated y],
    Groupoids.Hom.has (@AlgebraicSpace.Proper S) (graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.graph_quasiCompact_quasiSeparated :
    ∀ {S : Scheme.{u}}
    {X Y T : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack T] (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y)
    (hg : g ≫ y ≅ x) [QuasiSeparated y],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (graph x y g hg) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.graph_quasiCompact :
    ∀ {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x)
    [QuasiSeparated y],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S) (graph x y g hg))

#check (AlgebraicGeometry.AlgebraicStack.graph_isQuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y T : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack T]
    (x : X ⟶ T) (y : Y ⟶ T) (g : X ⟶ Y) (hg : g ≫ y ≅ x)
    [QuasiSeparated y],
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S) (graph x y g hg))

end AlgebraicGeometry.AlgebraicStack
