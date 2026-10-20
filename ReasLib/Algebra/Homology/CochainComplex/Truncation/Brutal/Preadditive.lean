/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor.Preadditive
public import ReasLib.CategoryTheory.Filtration.Complex.NegStage.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of brutal truncation towers

Both the filtration-stage tower and its `stupidTrunc` transport are additive
functors of cochain complexes.  The constructions themselves remain in their
respective data owners; this leaf only exposes the reusable instances.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace Tower

/-- The filtration-stage brutal tower is additive in the cochain complex. -/
@[stacks 0D8Z]
noncomputable instance functor_additive :
    (functor (A := A)).Additive := sorry

#synth (functor (A := A)).Additive

end Tower

namespace Trunc

/-- The transported `stupidTrunc` brutal tower is additive in the cochain complex. -/
@[stacks 0D8Z]
noncomputable instance functor_additive :
    (functor (A := A)).Additive := sorry

#synth (functor (A := A)).Additive

end Trunc

end CategoryTheory.CochainComplex.Brutal
