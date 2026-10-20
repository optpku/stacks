/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Injective.Characterizations
public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Dual

/-!
# Flat duals for a right internal Hom

This leaf isolates the Hom--tensor consequence of categorical flatness: internal Hom from a flat
object into an injective object is injective.  It deliberately does not assert that internal Hom
into an injective object is exact in its first variable; that conclusion needs additional
hypotheses and is false for a general closed abelian monoidal category.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (H : RightInternalHom C)

/-- Dualize, apply a chosen covariant replacement functor, and dualize again. -/
abbrev flatBidualFunctor (J : C) (F : C ⥤ C) : C ⥤ C :=
  (H.dualFunctor J).rightOp ⋙ F.op ⋙ H.dualFunctor J

/-- The value of the flat-bidual functor at `X`. -/
abbrev flatBidual (J : C) (F : C ⥤ C) (X : C) : C :=
  (H.flatBidualFunctor J F).obj X

section Abelian

variable [Abelian C]

/-- The categorical Hom--tensor form: the internal Hom from a flat object to an
injective object is injective. -/
theorem injective_dual (J P : C) [Injective J]
    [MonoidalCategory.IsFlat P] : Injective (H.dual J P) := by
  exact Injective.injective_of_adjoint (H.adj₂.adj P) J

/-- Lemma 19.8.3: if `F` functorially chooses flat objects, every value of the associated
flat-bidual functor is injective. -/
theorem injective_flatBidual (J : C) (F : C ⥤ C) [Injective J]
    [∀ X, MonoidalCategory.IsFlat (F.obj X)] (X : C) :
    Injective (H.flatBidual J F X) := by
  exact H.injective_dual J (F.obj (H.dual J X))

end Abelian

end CategoryTheory.RightInternalHom
