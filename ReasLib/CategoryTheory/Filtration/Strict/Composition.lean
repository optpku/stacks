/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.MonoEpi
public import ReasLib.CategoryTheory.Subobject.Image
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of Strict Morphisms

Strict filtered morphisms are stable under composition when the second underlying map is mono or
the first underlying map is epi.  The companion image and quotient formulas are exposed for
independent reuse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [HasImages C] [HasPullbacks C] [HasEqualizers C]
variable {A B D : FilteredObject C}

/-- A strict monomorphism sends an intersection with a filtration stage to the corresponding
intersection in its target. -/
theorem map_inf_of_strict_mono (g : B ⟶ D) [Mono g.hom] (hg : Strict g)
    (x : Subobject B.obj) (i : ℤ) :
    (Subobject.map g.hom).obj (x ⊓ B.filtration i) =
      (Subobject.map g.hom).obj x ⊓ D.filtration i := sorry

/-- Taking a quotient filtration is compatible, stagewise, with composition of the underlying
morphisms. -/
theorem quotient_comp [Balanced C] (f : A ⟶ B) (g : B ⟶ D) (i : ℤ) :
    A.filtration.quotient (f.hom ≫ g.hom) i =
      (A.filtration.quotient f.hom).quotient g.hom i := sorry

/-- If the second underlying map is mono, the composite of two strict filtered morphisms is
strict. -/
@[stacks 05SJ]
theorem strict_comp_of_mono [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Mono g.hom]
    (hf : Strict f) (hg : Strict g) : Strict (f ≫ g) := sorry

/-- If the first underlying map is epi, the composite of two strict filtered morphisms is
strict. -/
@[stacks 05SJ]
theorem strict_comp_of_epi [Balanced C] (f : A ⟶ B) (g : B ⟶ D) [Epi f.hom]
    (hf : Strict f) (hg : Strict g) : Strict (f ≫ g) := sorry

end CategoryTheory.FilteredObject.Hom
