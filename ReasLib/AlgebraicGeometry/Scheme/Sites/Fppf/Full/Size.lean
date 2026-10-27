/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Full
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Size

@[expose] public section

universe u

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- The full chosen big fppf site is closed under bounded-size representation
and countable scheme coproducts. -/
theorem isSizeClosed_full : ChosenBigSite.IsSizeClosed full.{u} := sorry

end AlgebraicGeometry.ChosenBigFppfSite
