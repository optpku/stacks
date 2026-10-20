/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSmoothLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalAtTarget.BaseChange

/-!
# Étale-smooth locality implications

A morphism property of algebraic spaces that is étale-smooth local on
source-and-target is étale local on the source, smooth local on the target,
stable under postcomposition with étale morphisms, and descends along étale
postcomposition.

Conversely, étale locality on the source and smooth locality on the target,
together with stability under postcomposition with open immersions, imply
étale-smooth locality on source-and-target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget

variable {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}

/-- A morphism property that is étale-smooth local on source-and-target is local
for étale covers of the source. -/
instance toIsLocalAtSource [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtSource (@etalePrecoverage S) :=
  sorry

/-- A morphism property that is étale-smooth local on source-and-target is local
for smooth covers of the target. -/
instance toIsLocalAtTarget [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.IsLocalAtTarget (smoothPrecoverage S) :=
  sorry

/-- A morphism property that is étale-smooth local on source-and-target is
preserved by postcomposition with an étale morphism. -/
instance toRespectsRightEtale [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.RespectsRight (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- A morphism property that is étale-smooth local on source-and-target descends
along postcomposition with an étale morphism. -/
instance toHasOfPostcompEtale [IsEtaleSmoothLocalAtSourceAndTarget P] :
    P.HasOfPostcompProperty (@Etale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Étale locality on the source and smooth locality on the target, together with
stability under postcomposition with open immersions, implies étale-smooth
locality on source-and-target. -/
@[instance 100]
theorem of_isLocalAtSource_isLocalAtTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtSource etalePrecoverage]
    [P.IsLocalAtTarget (smoothPrecoverage S)]
    [P.RespectsRight (@IsOpenImmersion S : MorphismProperty (AlgebraicSpace S))] :
    IsEtaleSmoothLocalAtSourceAndTarget P :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsEtaleSmoothLocalAtSourceAndTarget
