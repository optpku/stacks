/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.Octahedron
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.10.2

The reusable content is owned by shape-independent degreewise-split quotient rows and their
homotopy-category triangle API.  Termwise composition is supplied by the multiplicative morphism
property, while the final existence statement is a thin bridge to the ambient octahedron axiom.
-/

namespace HomologicalComplex

#check @termwiseSplitMono_comp
#check @DegreewiseSplitQuotient
#check @DegreewiseSplitQuotient.shortComplex
#check @DegreewiseSplitQuotient.shortComplex_isDegreewiseSplit
#check @DegreewiseSplitQuotient.termwiseSplitMono
#check @DegreewiseSplitQuotient.termwiseSplitEpi
#check @DegreewiseSplitQuotient.triangleh
#check @DegreewiseSplitQuotient.triangle
#check @DegreewiseSplitQuotient.triangle_distinguished

/- Lemma 13.10.2: the three degreewise-split quotient rows associated to two composable maps and
their composite determine an octahedron in the homotopy category. -/
@[stacks 014R]
#check @DegreewiseSplitQuotient.nonempty_octahedron

end HomologicalComplex
