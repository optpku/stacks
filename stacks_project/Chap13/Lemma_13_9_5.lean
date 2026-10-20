/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Strictification
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.5

The strictification statements are owned by
`ReasLib.Algebra.Homology.CochainComplex.Strictification`.  This file keeps the source label and
the two views used by the chapter: the homotopy-level replacement and its homotopy-category
representative.
-/

open CategoryTheory ComplexShape HomologicalComplex HomotopyCategory

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B D E : CochainComplex C ℤ}

/- Lemma 13.9.5 (1): strictify the right map along a termwise split monomorphism. -/
@[stacks 014H]
#check @exists_homotopic_rightMap_of_termwiseSplitMono

/- Lemma 13.9.5 (2): strictify the left map along a termwise split epimorphism. -/
@[stacks 014H]
#check @exists_homotopic_leftMap_of_termwiseSplitEpi

/- The admissibility views are the canonical cochain-complex specializations. -/
@[stacks 014H]
#check @exists_homotopic_rightMap_of_admissibleMono
@[stacks 014H]
#check @exists_homotopic_leftMap_of_admissibleEpi

/- The quotient-square views retain the original homotopy-category morphism. -/
@[stacks 014H]
#check @exists_rightMap_eq_in_homotopyCategory_of_termwiseSplitMono
@[stacks 014H]
#check @exists_leftMap_eq_in_homotopyCategory_of_termwiseSplitEpi

end CochainComplex
