/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.GeometricallyIrreducible.AdjoinSimple
import StacksCheckRecall

@[expose] public section

/-!
# Transcendental simple-adjoin extension

Lemma 10.47.11 is a direct recall of the shared simple-adjoin criterion.  The owner keeps the
chosen `M⟮x⟯ → L⟮x⟯` algebra named and non-instance, avoiding an element-dependent global instance.

@stack 0G32
-/

/- Lemma 10.47.11 (Tag 0G32). -/
@[stacks 0G32]
#check @AlgebraicGeometry.FieldExtension.GeometricallyIrreducible.AdjoinSimple.of_transcendental

end
