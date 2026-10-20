/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-!
# Composition of explicit quasi-inverses

This file owns the direct composition of quasi-inverse data and its computation interface.
-/

@[expose] public section

universe vA uA vB uB vC uC

namespace CategoryTheory.Functor.QuasiInverse

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {C : Type uC} [Category.{vC} C]
variable {F : A ⥤ B} {G : B ⥤ C}

/-- The canonical unit isomorphism for the composite of explicit quasi-inverse data. -/
def transUnitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    𝟭 A ≅ (F ⋙ G) ⋙ (f.inverse ⋙ e.inverse) :=
  e.unitIso ≪≫
    Functor.isoWhiskerRight
      (F.rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft F f.unitIso ≪≫
        (Functor.associator F G f.inverse).symm)
      e.inverse ≪≫
    Functor.associator (F ⋙ G) f.inverse e.inverse

/-- The canonical counit isomorphism for the composite of explicit quasi-inverse data. -/
def transCounitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    (f.inverse ⋙ e.inverse) ⋙ (F ⋙ G) ≅ 𝟭 C :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft f.inverse e.counitIso ≪≫
        f.inverse.rightUnitor)
      G ≪≫
    f.counitIso

/-- Explicit quasi-inverse data compose without passing through a chosen equivalence. In
particular, both supplied comparison isomorphisms remain visible through the named composite
unit and counit owners. -/
def trans (e : QuasiInverse F) (f : QuasiInverse G) : QuasiInverse (F ⋙ G) where
  inverse := f.inverse ⋙ e.inverse
  unitIso := transUnitIso e f
  counitIso := transCounitIso e f

/-- The inverse in a composite of explicit quasi-inverse data is the reverse composite of the
two inverses. -/
@[simp]
theorem trans.inverse (e : QuasiInverse F) (f : QuasiInverse G) :
    (e.trans f).inverse = f.inverse ⋙ e.inverse := sorry

/-- The unit in a composite of explicit quasi-inverse data is the canonical composite unit. -/
@[simp]
theorem trans.unitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    (e.trans f).unitIso = transUnitIso e f := sorry

/-- The counit in a composite of explicit quasi-inverse data is the canonical composite
counit. -/
@[simp]
theorem trans.counitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    (e.trans f).counitIso = transCounitIso e f := sorry

end CategoryTheory.Functor.QuasiInverse
