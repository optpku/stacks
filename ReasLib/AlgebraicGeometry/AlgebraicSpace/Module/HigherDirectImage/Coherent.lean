/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support.Closed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubset.Proper

/-!
# Coherence of higher direct images with proper support

Every higher direct image of a coherent module along a proper morphism of algebraic
spaces to a locally Noetherian algebraic space is coherent.
The same holds along a locally of finite type morphism when the coherent module
has support proper over the target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Every higher direct image of a coherent module along a proper morphism of algebraic
spaces with locally Noetherian target is coherent. -/
instance higherDirectImage_isCoherent_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (i : ℕ) :
    (higherDirectImage f F i).IsCoherent :=
  sorry

/-- Every higher direct image of a coherent module with proper support along a locally
of finite type morphism of algebraic spaces with locally Noetherian target is coherent. -/
@[stacks 08GC]
theorem higherDirectImage_isCoherent_of_properSupport
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (hF : ClosedSubset.ProperOver f (closedSupport F)) (p : ℕ) :
    (higherDirectImage f F p).IsCoherent :=
  sorry

/-- Proper support of a coherent module ensures coherence of its higher direct images
along a locally of finite type morphism to a locally Noetherian algebraic space. -/
instance instIsCoherentHigherDirectImageOfProperSupport
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    [hF : Fact (ClosedSubset.ProperOver f (closedSupport F))] (p : ℕ) :
    (higherDirectImage f F p).IsCoherent :=
  higherDirectImage_isCoherent_of_properSupport f F hF.out p

end AlgebraicGeometry.AlgebraicSpace.Modules
