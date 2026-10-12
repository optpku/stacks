/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import stacks_project.Chap103.Definition_103_14_1_Sites
public import stacks_project.Chap103.«103_15_1_1_Smooth»

/-!
# Restricted lisse-étale and flat-fppf site functors

A smooth morphism of algebraic stacks sends lisse objects to lisse objects and
therefore lifts to a functor of lisse-étale sites. A flat morphism likewise
lifts to a functor of flat-fppf sites. Both restricted functors are continuous
and cocontinuous.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Smoothness of `f` sends lisse objects of `X` to lisse objects of `Y`. -/
theorem isLisse.map (f : X ⟶ Y) [Smooth f] {x : X.total} (hx : isLisse X x) :
    isLisse Y ((toFunctor f).obj x) :=
  sorry

/-- Flatness of `f` sends flat objects of `X` to flat objects of `Y`. -/
theorem isFlat.map (f : X ⟶ Y) [Flat f] {x : X.total} (hx : isFlat X x) :
    isFlat Y ((toFunctor f).obj x) :=
  sorry

/-- The functor of lisse-étale sites induced by a smooth morphism of algebraic
stacks. -/
def lisseEtaleMap (f : X ⟶ Y) [Smooth f] : lisseEtaleSite X ⥤ lisseEtaleSite Y :=
  (isLisse Y).lift (lisseEtaleInclusion X ⋙ toFunctor f) fun x ↦ isLisse.map f x.property

/-- The functor of flat-fppf sites induced by a flat morphism of algebraic
stacks. -/
def flatFppfMap (f : X ⟶ Y) [Flat f] : flatFppfSite X ⥤ flatFppfSite Y :=
  (isFlat Y).lift (flatFppfInclusion X ⋙ toFunctor f) fun x ↦ isFlat.map f x.property

/-- The lisse-étale restriction of `f` composed with the inclusion of `Y` is the
inclusion of `X` composed with the total functor of `f`. -/
def lisseEtaleMap_comp_ι (f : X ⟶ Y) [Smooth f] :
    lisseEtaleMap f ⋙ lisseEtaleInclusion Y ≅
      lisseEtaleInclusion X ⋙ toFunctor f :=
  (isLisse Y).liftCompιIso (lisseEtaleInclusion X ⋙ toFunctor f)
    fun x ↦ isLisse.map f x.property

/-- The flat-fppf restriction of `f` composed with the inclusion of `Y` is the
inclusion of `X` composed with the total functor of `f`. -/
def flatFppfMap_comp_ι (f : X ⟶ Y) [Flat f] :
    flatFppfMap f ⋙ flatFppfInclusion Y ≅
      flatFppfInclusion X ⋙ toFunctor f :=
  (isFlat Y).liftCompιIso (flatFppfInclusion X ⋙ toFunctor f)
    fun x ↦ isFlat.map f x.property

/-- The lisse-étale restriction of a smooth morphism is continuous. -/
instance lisseEtaleMap.instIsContinuous (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleMap f).IsContinuous (lisseEtaleTopology X) (lisseEtaleTopology Y) :=
  sorry

/-- The lisse-étale restriction of a smooth morphism is cocontinuous. -/
instance lisseEtaleMap.instIsCocontinuous (f : X ⟶ Y) [Smooth f] :
    (lisseEtaleMap f).IsCocontinuous (lisseEtaleTopology X) (lisseEtaleTopology Y) :=
  sorry

/-- The flat-fppf restriction of a flat morphism is continuous. -/
instance flatFppfMap.instIsContinuous (f : X ⟶ Y) [Flat f] :
    (flatFppfMap f).IsContinuous (flatFppfTopology X) (flatFppfTopology Y) :=
  sorry

/-- The flat-fppf restriction of a flat morphism is cocontinuous. -/
instance flatFppfMap.instIsCocontinuous (f : X ⟶ Y) [Flat f] :
    (flatFppfMap f).IsCocontinuous (flatFppfTopology X) (flatFppfTopology Y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
