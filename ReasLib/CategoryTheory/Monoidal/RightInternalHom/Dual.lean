/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Basic

/-!
# Dual functors from a right internal Hom

This leaf contains the variance bookkeeping for dualization into a fixed object.  It deliberately
does not require a braiding: the braiding is needed only when constructing the canonical map to
the bidual.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightInternalHom

variable (H : RightInternalHom C)

/-- The contravariant dual functor with values in a fixed object `J`. -/
@[stacks 01DR "dual functor"]
abbrev dualFunctor (J : C) : Cᵒᵖ ⥤ C :=
  H.hom ⋙ (evaluation C C).obj J

/-- The dual of `X` with values in `J`. -/
abbrev dual (J X : C) : C :=
  (H.dualFunctor J).obj (op X)

/-- The covariant double-dual functor associated to `J`. -/
@[stacks 01DS "bidual functor"]
abbrev bidualFunctor (J : C) : C ⥤ C :=
  (H.dualFunctor J).rightOp ⋙ H.dualFunctor J

end RightInternalHom

end CategoryTheory
