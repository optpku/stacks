module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Point
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange.BoundedBelow
public import Mathlib.Topology.SeparatedMap
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Point-fibre specialization of bounded-below base change

This leaf owns the point-inclusion specialization used to identify a stalk of a derived
pushforward with derived sections on the fibre.  The square and the base-change map are inherited
from the generic bounded-below flat base-change API; only the topological hypotheses that make the
map invertible are specific to this result.
-/

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits
open scoped RingedSpace.Hom

-- The point inclusion is flat, and its pullback projection has the existing flatness witness.
attribute [local instance] RingedSpace.Hom.IsFlat.pullbackFst

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom.BoundedBaseChange

/-- The pullback square formed by a morphism `f` and the point inclusion at `y`. -/
@[stacks 09V5 "point-inclusion pullback square"]
theorem pointInclusionCommSq
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)
    [HasPullback f (pointInclusion y)] :
    CommSq
      (pullback.fst f (pointInclusion y))
      (pullback.snd f (pointInclusion y))
      f
      (pointInclusion y) := sorry

/-- Lemma 20.18.1 (09V5): the canonical bounded-below point-fibre base-change map is an
isomorphism under the closedness, separatedness, and quasi-compact-fibre hypotheses. -/
@[stacks 09V5 "point-fibre base-change isomorphism"]
theorem pointInclusionMap_isIso
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)
    [HasPullback f (pointInclusion y)]
    (hclosed : IsClosedMap f.hom.base)
    (hseparated : IsSeparatedMap f.hom.base)
    (hyqc : IsCompact (f.hom.base ⁻¹' ({y} : Set Y)))
    (E : DerivedCategory.Plus X.Modules) :
    IsIso (app (pointInclusionCommSq f y) E) := sorry

/-- Lemma 20.18.1 (09V5): any bounded-below point-fibre base-change map satisfying the canonical
comparison equation is an isomorphism under the stated hypotheses. -/
@[stacks 09V5 "point-fibre base-change isomorphism for specified maps"]
theorem isIso_of_isMap
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)
    [HasPullback f (pointInclusion y)]
    (hclosed : IsClosedMap f.hom.base)
    (hseparated : IsSeparatedMap f.hom.base)
    (hyqc : IsCompact (f.hom.base ⁻¹' ({y} : Set Y)))
    (E : DerivedCategory.Plus X.Modules)
    {η : (source f (pointInclusion y)).obj E ⟶
      (target (pullback.fst f (pointInclusion y))
        (pullback.snd f (pointInclusion y))).obj E}
    (hη : IsMapAt (pointInclusionCommSq f y) E η) :
    IsIso η := sorry

end AlgebraicGeometry.RingedSpace.Hom.BoundedBaseChange
