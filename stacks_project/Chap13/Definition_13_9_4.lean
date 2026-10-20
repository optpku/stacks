/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomologicalComplex.TermwiseSplit
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.9.4

Termwise split monomorphisms and epimorphisms are shape-independent morphism properties of
homological complexes.  Their `_iff` API recovers the textbook componentwise wording for cochain
complexes without creating a chapter-local wrapper.
-/

namespace HomologicalComplex

@[stacks 014G]
#check @termwiseSplitMono
@[stacks 014G]
#check @termwiseSplitMono_iff
@[stacks 014G]
#check @termwiseSplitEpi
@[stacks 014G]
#check @termwiseSplitEpi_iff

end HomologicalComplex
