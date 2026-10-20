/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Stalk
import StacksCheckRecall

/-!
# Lemma 21.46.10

The reusable owner first treats an arbitrary conservative indexed family of site points and
then specializes to sites with enough points.
-/

@[expose] public section

/- Lemma 21.46.10 (0DJJ): Tor-amplitude is detected by all derived point stalks on a site
with enough points. -/
@[stacks 0DJJ] #check
  @RingedSite.Hom.ModuleDerived.hasTorAmplitudeIn_iff_forall_stalk_of_hasEnoughPoints

#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn.stalk
#check
  @RingedSite.Hom.ModuleDerived.hasTorAmplitudeIn_iff_forall_stalk_of_isConservativeFamily
#check @CategoryTheory.GrothendieckTopology.Point.moduleStalkDerived

end
