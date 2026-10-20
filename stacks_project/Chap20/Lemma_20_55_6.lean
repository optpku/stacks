/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.6 (0F8P): a quasi-isomorphism between complexes on which a locally principal
regular ideal acts monomorphically degreewise induces a quasi-isomorphism of eta complexes. -/
@[stacks 0F8P]
#check @IdealSheaf.Eta.functor_map_quasiIso

@[stacks 0F8P "functorial eta construction"]
#check @IdealSheaf.Eta.functor

@[stacks 0F8P "eta map"]
#check @IdealSheaf.Eta.map

@[stacks 0F8P "eta domain"]
#check @IdealSheaf.Eta.Domain

#check @IdealSheaf.Eta.map_quasiIso
#check @IdealSheaf.IsRegularPrincipal.isInvertible
