/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.InternalHom
import StacksCheckRecall

/-!
# Internal Hom and stalks

The reusable comparison and both finiteness clauses live in ReasLib.  This file records the
source correspondence only.
-/

@[expose] public section

open AlgebraicGeometry

/- Lemma 17.22.4 (01CP), canonical map: the stalk of the sheaf internal Hom maps to the internal
Hom of the stalk modules. -/
@[stacks 01CP "canonical map"]
#check @RingedSpace.InternalHom.Stalk.comparison

/- The finite-presentation comparison is available as explicit Iso data. -/
#check @RingedSpace.InternalHom.Stalk.comparisonIso
#check @RingedSpace.InternalHom.Stalk.comparisonInv
#check @RingedSpace.InternalHom.Stalk.comparison_hom_inv_id
#check @RingedSpace.InternalHom.Stalk.comparison_inv_hom_id
#check @RingedSpace.InternalHom.Stalk.comparisonIso_hom
#check @RingedSpace.InternalHom.Stalk.comparisonIso_inv

/- Lemma 17.22.4 (01CP), first clause: finite type of the source makes the comparison
injective. -/
@[stacks 01CP "finite-type clause"]
#check @RingedSpace.InternalHom.Stalk.comparison_injective

/- The same finite-type conclusion is registered for categorical downstream use. -/
#check @RingedSpace.InternalHom.Stalk.comparison_mono

/- Lemma 17.22.4 (01CP), second clause: finite presentation of the source makes the comparison
an isomorphism. -/
@[stacks 01CP "finite-presentation clause"]
#check @RingedSpace.InternalHom.Stalk.comparison_isIso

/- The explicit comparison is characterized by its uncurried evaluation map. -/
#check @RingedSpace.InternalHom.Stalk.uncurry_comparison

/- The comparison is natural in the target and contravariantly natural in the source. -/
#check @RingedSpace.InternalHom.Stalk.comparison_naturality
#check @RingedSpace.InternalHom.Stalk.comparisonInv_naturality
#check @RingedSpace.InternalHom.Stalk.comparison_naturality_left

/- Fixed-source comparisons assemble into a reusable natural transformation and natural Iso. -/
#check @RingedSpace.InternalHom.Stalk.sourceFunctor
#check @RingedSpace.InternalHom.Stalk.targetFunctor
#check @RingedSpace.InternalHom.Stalk.natTrans
#check @RingedSpace.InternalHom.Stalk.natTrans_isIso
#check @RingedSpace.InternalHom.Stalk.comparisonNatIso
#check @RingedSpace.InternalHom.Stalk.comparisonNatIso_hom
#check @RingedSpace.InternalHom.Stalk.comparisonInvNatTrans
#check @RingedSpace.InternalHom.Stalk.comparisonNatIso_inv
#check @RingedSpace.InternalHom.Stalk.comparisonNatIso_inv_app
