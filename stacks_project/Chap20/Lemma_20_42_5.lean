/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Source
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.42.5 (0A8V): composition of derived internal Homs on a ringed space is the
source-order composition map in any braided closed monoidal category. -/
@[stacks 0A8V]
#check @CategoryTheory.MonoidalClosed.Source.comp

#check @CategoryTheory.MonoidalClosed.Source.comp_spec

end AlgebraicGeometry.RingedSpace
