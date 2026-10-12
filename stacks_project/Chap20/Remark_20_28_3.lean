/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

/- [stacks 08HY] Remark 20.28.3: after choosing the two derived adjunctions and a comparison
isomorphism `L(g)^* ⋙ L(f')^* ≅ L(f)^* ⋙ L(g')^*`, the unbounded base-change component is the
canonical mate `L(g)^* R(f)_* K ⟶ R(f')_* L(g')^* K`. -/

namespace AlgebraicGeometry.RingedSpace

#check @RingedSpace.Hom.DerivedBaseChange.source
#check @RingedSpace.Hom.DerivedBaseChange.target
#check @RingedSpace.Hom.DerivedBaseChange.pullbackIsoOfCompIso
#check @RingedSpace.Hom.DerivedBaseChange.map
#check @RingedSpace.Hom.DerivedBaseChange.app
#check @RingedSpace.Hom.DerivedBaseChange.IsMapAt
#check @RingedSpace.Hom.DerivedBaseChange.map_isMapAt
#check @RingedSpace.Hom.DerivedBaseChange.IsMapAt.eq_app

-- Compatibility names retained while the later composition remarks migrate to the short owner.
#check @derivedBaseChangeSource
#check @derivedBaseChangeTarget
#check @unboundedDerivedBaseChangeMapAdjoint
#check @unboundedDerivedBaseChangeMap
#check @IsUnboundedDerivedBaseChangeMap
#check @unboundedDerivedBaseChangeMap_spec
#check @eq_unboundedDerivedBaseChangeMap

end AlgebraicGeometry.RingedSpace
