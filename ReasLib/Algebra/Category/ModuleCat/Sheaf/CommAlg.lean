/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.Linear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.DifferentialGraded
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject

/-!
# Differential graded modules over commutative algebra sheaves

This lightweight umbrella re-exports the coefficient-generic linear, differential graded, and
underived tensor-with-object owners.  Downstream derived tensor and tensor-Hom developments should
import `ReasLib.Algebra.Category.ModuleCat.Sheaf.CommAlg.TensorWithObject.Derived` explicitly; keeping
that boundary here prevents the base `ReasLib.Algebra` umbrella from importing the entire derived
stack.

The sibling `TensorWithObject/Adjunction.lean` leaf owns sectionwise currying and the underived
homotopy adjunction.  Consumers that need derived tensor-Hom, regular-object comparisons, or the
compact-generator full-faithfulness criterion should import
`TensorWithObject/Derived.lean` directly; the derived boundary remains explicit by design.
-/

@[expose] public section
