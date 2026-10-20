/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Adjunction

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.SmallToBig

#check etalePiInverseImage
#check etalePiPushforward
#check etalePiAdjunction
#check etalePiDerivedAdjunction_unit_isIso

end AlgebraicGeometry.Scheme.Etale.SmallToBig
