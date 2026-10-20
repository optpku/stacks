/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Correspondence.Graded.GraphFunctor

open CategoryTheory

universe u

/- Lemma 45.3.4: The graph construction is a contravariant functor from smooth
projective schemes over `k` to degree-zero rational Chow correspondences. -/
@[stacks 0FG3] #check (@AlgebraicGeometry.Correspondence.Graded.graphFunctor :
  (k : Type u) → [Field k] →
    (AlgebraicGeometry.Correspondence.Graded.SchemeCategory k)ᵒᵖ ⥤
      AlgebraicGeometry.Correspondence.Graded.DegreeZero (k := k))
