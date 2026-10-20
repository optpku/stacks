module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.Morphism
public import stacks_project.Chap103.Definition_103_14_1_Sites
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-! # Restricted lisse-étale and flat-fppf site functors -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.isLisse.map :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f] {x : X.total} (hx : isLisse X x),
    isLisse Y ((toFunctor f).obj x))

#check (AlgebraicGeometry.AlgebraicStack.isFlat.map :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f] {x : X.total} (hx : isFlat X x),
    isFlat Y ((toFunctor f).obj x))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    lisseEtaleSite X ⥤ lisseEtaleSite Y)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    flatFppfSite X ⥤ flatFppfSite Y)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap_comp_ι :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    lisseEtaleMap f ⋙ lisseEtaleInclusion Y ≅
      lisseEtaleInclusion X ⋙ toFunctor f)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap_comp_ι :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    flatFppfMap f ⋙ flatFppfInclusion Y ≅
      flatFppfInclusion X ⋙ toFunctor f)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.instIsContinuous :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    (lisseEtaleMap f).IsContinuous (lisseEtaleTopology X) (lisseEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleMap.instIsCocontinuous :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Smooth f],
    (lisseEtaleMap f).IsCocontinuous (lisseEtaleTopology X) (lisseEtaleTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.instIsContinuous :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    (flatFppfMap f).IsContinuous (flatFppfTopology X) (flatFppfTopology Y))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfMap.instIsCocontinuous :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Flat f],
    (flatFppfMap f).IsCocontinuous (flatFppfTopology X) (flatFppfTopology Y))

