/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.LocalHom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 18.40.9 (04HA): locality is a property of the bundled ringed-site morphism and its
canonical inverse-image structure-sheaf map. -/
@[stacks 04HA]
#check @RingedSite.Hom.IsLocal

#check @RingedSite.Hom.isLocal_iff
#check @RingedSite.Hom.isLocal_iff_unitsSquare
