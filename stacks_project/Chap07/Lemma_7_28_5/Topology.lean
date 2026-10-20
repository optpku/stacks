/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.CostructuredArrowTopology
public import StacksCheckRecall.CommandCrossRef

/-!
# Lemma 7.28.5 comma-site topology

The induced topology on a costructured arrow category and the projection API
are reusable site infrastructure.  They are owned by ReasLib; this Chapter 7
leaf records the source-facing recall surface only.
-/

@[expose] public section

/- Lemma 7.28.5 (0D5R): the comma category `CostructuredArrow u V` receives
the topology whose covers are detected after projection to the source site.
The projection preserves covers and compatible families, hence is continuous. -/
@[stacks 0D5R] #check @CategoryTheory.cocontinuousOverTopology

@[stacks 0D5R] #check @CategoryTheory.cocontinuousOverTopology.coverPreserving

@[stacks 0D5R] #check @CategoryTheory.cocontinuousOverTopology.compatiblePreserving

@[stacks 0D5R] #check @CategoryTheory.cocontinuousOverTopology.isContinuous
