/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Refinement.Total
import StacksCheckRecall

/-!
# Total Čech refinement

@stack 08BM

20.25.0.2 is the source-facing view of the reusable refinement tower.  The coefficient-free
predicate and formal-coproduct map live in `Cech.Refinement`; this entry only exposes their row,
double-complex, and total-complex lifts.
-/

@[expose] public section

open CategoryTheory.Cech.Refinement

/- 20.25.0.2: an indexed-open refinement induces the canonical map on total Čech complexes. -/
@[stacks 08BM "row Cech refinement"]
#check @CategoryTheory.Cech.Refinement.row

@[stacks 08BM "double Cech refinement"]
#check @CategoryTheory.Cech.Refinement.double

@[stacks 08BM "total Cech refinement"]
#check @CategoryTheory.Cech.Refinement.total

@[stacks 08BM "total Cech refinement map"]
#check @CategoryTheory.Cech.Refinement.map

@[stacks 08BM "total Cech refinement map as a totalized double map"]
#check @CategoryTheory.Cech.Refinement.map_eq_total_map

@[stacks 08BM "naturality of the total Cech refinement map"]
#check @CategoryTheory.Cech.Refinement.map_naturality

end
