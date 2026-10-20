/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Presheaf.Representability
public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

open CategoryTheory

open AlgebraicGeometry

/- Definition 26.15.1: representability of a contravariant set-valued
functor is the canonical predicate `Functor.IsRepresentable`. -/
@[stacks 01JG] #check Functor.IsRepresentable

/- Definition 26.15.1: the universe-polymorphic universal-element characterization. -/
@[stacks 01JG] #check Functor.IsRepresentable.iff_exists_isRepresentedBy

/- Same-universe Yoneda-isomorphism presentation, retained as a convenient bridge. -/
#check isRepresentable_iff_exists_yoneda_obj_iso

section Scheme

universe u

variable (F : Scheme.{u}ᵒᵖ ⥤ Type u)

/- Source-facing specialization: the functor in Definition 26.15.1 is a presheaf on schemes. -/
@[stacks 01JG] #check F.IsRepresentable
@[stacks 01JG] #check isRepresentable_iff_exists_yoneda_obj_iso F

end Scheme
