/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

import StacksCheckRecall
public import ReasLib.CategoryTheory.Limits.Exactness

@[expose] public section

/- Remark 7.14.8 (00X7) (1): left exactness is precisely preservation of finite limits. -/
@[stacks 00X7 "left exactness and finite-limit preservation"] #check @CategoryTheory.leftExactFunctor_iff

/- Remark 7.14.8 (00X7) (2): when the source has finite limits, left exactness is precisely
preservation of the terminal object and pullbacks. This is the geometric formulation used in
Proposition 7.14.7. -/
@[stacks 00X7 "terminal objects and pullbacks characterize left exactness"] #check @CategoryTheory.leftExactFunctor.iff_preservesTerminal_and_pullbacks
