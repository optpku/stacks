/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GenericFlatness.Locus.Local
import StacksCheckRecall

@[expose] public section

/-!
# Density from a Localized Basic-Open Cover

The source statement retains its dense open and its localized good loci.  The
shared topological form is recalled separately below.

@stack 051Y
-/

/- The source-facing localized criterion. -/
@[stacks 051Y "localized basic-open cover"]
#check @GenericFlatness.dense_of_localized_cover

/- The reusable topological core. -/
@[stacks 051Y "topological local-to-global core"]
#check @GenericFlatness.dense_of_dense_basicOpen_cover
