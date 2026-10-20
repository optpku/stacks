/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Types.Constant
import StacksCheckRecall

@[expose] public section

open TopCat

/- The preceding definition realizes the textbook constant sheaf as continuous maps into the
discrete space on `A`; by `IsLocallyConstant.iff_continuous`, this is exactly the sheaf of locally
constant `A`-valued functions. Recalling its explicit comparison morphism preserves the source map
instead of introducing another isomorphic wrapper. -/

/- Example 6.17.4 (1): the map from the constant presheaf to constant maps induces the canonical
comparison from its sheafification to the sheaf of locally constant `A`-valued functions. -/
@[stacks 0081 "comparison induced by constant maps"]
recall TopCat.Sheaf.Constant.toDiscrete

/- Example 6.17.4 (2): this canonical comparison is an isomorphism, so the sheafification of the
constant presheaf with value `A` is the constant sheaf with value `A`. -/
@[stacks 0081 "sheafification identifies the constant sheaf"]
recall TopCat.Sheaf.Constant.toDiscrete_isIso
