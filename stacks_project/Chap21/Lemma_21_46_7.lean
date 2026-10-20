/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.46.7

The tensor-product closure theorem is owned by the reusable ringed-site Tor-dimension library;
this file records the source label and its main downstream consequences.
-/

/- Lemma 21.46.7 (09JA): Tor-amplitude intervals add under derived tensor product. -/
@[stacks 09JA]
#check @RingedSite.Hom.ModuleDerived.HasTorAmplitudeIn.tensor

#check @RingedSite.Hom.ModuleDerived.HasFlatRepresentativeIn.tensor
#check @RingedSite.Hom.ModuleDerived.HasFiniteTorDimension.tensor

end
