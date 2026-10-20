/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (S : ShortComplex C)

/- Definition 12.5.9 [010F]: a split short complex is exactly a short complex equipped with the
canonical `ShortComplex.Splitting` data. -/
@[stacks 010F]
#check (Nonempty S.Splitting : Prop)

/- The canonical owner exposes the retraction, section, and direct-sum identity as structure
fields, without a chapter-local existential wrapper. -/
#check @ShortComplex.Splitting.mk

#check @ShortComplex.Splitting.splitMono_f

#check @ShortComplex.Splitting.splitEpi_g

#check @ShortComplex.Splitting.isoBinaryBiproduct

end
