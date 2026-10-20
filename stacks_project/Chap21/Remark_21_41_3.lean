/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.SimplicialAugmentation
import StacksCheckRecall

/-!
# Remark 21.41.3

The constant-coefficient and augmentation constructions are owned by
`CategoryTheory.SimplicialSite.Derived`.  This file is the compact source-facing recall for the
remark.
-/

@[expose] public section

open CategoryTheory
open scoped CategoryTheory SimplicialSite

namespace CategoryTheory.SimplicialSite.Derived

/- Remark 21.41.3: for an augmentation
`ε : A ⟶ constantStructureSheaf 𝒪` whose alternating-face map
`augmentationComplexMap ε` is a quasi-isomorphism, the composite
`augmentationLowerShriek ε` is the exact `𝒪`-valued lower-shriek functor.  Its comparison with
`lowerShriek A` after forgetting module structure is exposed below, together with the constant
coefficient case. -/
@[stacks 09D3 "Remark 21.41.3 constant structure sheaf"]
#check @constantStructureSheaf

@[stacks 09D3 "Remark 21.41.3 constant projection comparison"]
#check @constantProjectionIso

/- Remark 21.41.3: the constant module lower shriek and its forgetful functor. -/
@[stacks 09D3 "Remark 21.41.3 constant lower shriek"]
#check @constantLowerShriek

@[stacks 09D3 "Remark 21.41.3 constant forgetful functor"]
#check @constantForget

@[stacks 09D3 "Remark 21.41.3 constant underlying comparison"]
#check @constantLowerShriek.underlyingComparison

@[stacks 09D3 "Remark 21.41.3 constant underlying comparison isomorphism"]
#check @constantLowerShriek.underlyingComparison_isIso

@[stacks 09D3 "Remark 21.41.3 constant underlying natural isomorphism"]
#check @constantLowerShriek.underlyingComparisonIso

@[stacks 09D3 "Remark 21.41.3 constant forgetful comparison"]
#check @constantLowerShriek.forget_isomorphic

@[stacks 09D3 "Remark 21.41.3 constant shift comparison"]
#check @constantLowerShriek.commShift

@[stacks 09D3 "Remark 21.41.3 constant triangulated structure"]
#check @constantLowerShriek.isTriangulated

/- Remark 21.41.3: the additive augmentation and alternating-face map. -/
@[stacks 09D3 "Remark 21.41.3 additive augmentation"]
#check @additiveAugmentation

@[stacks 09D3 "Remark 21.41.3 augmentation complex map"]
#check @augmentationComplexMap

/- Remark 21.41.3: the augmentation module lower shriek and the comparison conclusions. -/
@[stacks 09D3 "Remark 21.41.3 augmentation lower shriek"]
#check @augmentationLowerShriek

@[stacks 09D3 "Remark 21.41.3 unit comparison"]
#check @unitComparison.isIso

@[stacks 09D3 "Remark 21.41.3 unit comparison functor bridge"]
#check @augmentationLowerShriek.forget_isomorphic_of_unit

@[stacks 09D3 "Remark 21.41.3 unit comparison object bridge"]
#check @augmentationLowerShriek.forget_obj_isomorphic_of_unit

@[stacks 09D3 "Remark 21.41.3 functorial comparison"]
#check @augmentationLowerShriek.forget_isomorphic

@[stacks 09D3 "Remark 21.41.3 objectwise comparison"]
#check @augmentationLowerShriek.forget_obj_isomorphic

@[stacks 09D3 "Remark 21.41.3 augmentation shift comparison"]
#check @augmentationLowerShriek.commShift

@[stacks 09D3 "Remark 21.41.3 triangulated structure"]
#check @augmentationLowerShriek.isTriangulated

@[stacks 09D3 "Remark 21.41.3 projection triangulated structure"]
#check @lowerShriek.hasTriangulatedStructure

end CategoryTheory.SimplicialSite.Derived
