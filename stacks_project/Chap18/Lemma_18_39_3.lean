/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 18.39.3: a conservative family of points detects flat module sheaves. -/
@[stacks 05VC]
#check @SheafOfModules.RingedSite.isFlat_iff_forall_isFlatAt

/- Lemma 18.39.3, ringed-space specialization: stalkwise flatness agrees with the canonical
opens-site monoidal notion. -/
@[stacks 05VC "ringed-space specialization"]
#check @SheafOfModules.isFlat_iff_ringedSite_isFlat
