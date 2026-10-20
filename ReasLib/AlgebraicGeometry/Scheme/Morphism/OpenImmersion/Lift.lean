/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsOpenImmersion

/-- Lifting a morphism through an open immersion preserves stalk isomorphisms when the original
stalk maps are isomorphisms. -/
theorem lift_stalkMap_isIso
    {X Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (f : X ⟶ Z)
    [∀ x : X, IsIso (f.stalkMap x)] (h : Set.range f ⊆ Set.range j) (x : X) :
    IsIso ((IsOpenImmersion.lift j f h).stalkMap x) := by
  have hStage :
      IsIso (j.stalkMap ((IsOpenImmersion.lift j f h) x)) := by
    exact (IsOpenImmersion.iff_isIso_stalkMap (f := j)).mp inferInstance |>.2 _
  have hComp :
      IsIso (j.stalkMap ((IsOpenImmersion.lift j f h) x) ≫
        (IsOpenImmersion.lift j f h).stalkMap x) := by
    rw [← Scheme.Hom.stalkMap_comp]
    rw [Scheme.Hom.stalkMap_congr_hom
      (f := (IsOpenImmersion.lift j f h) ≫ j)
      (g := f) (IsOpenImmersion.lift_fac j f h) (x := x)]
    have hx :
        ((IsOpenImmersion.lift j f h) ≫ j) x = f x := by
      simpa using
        congrArg (fun k : X ⟶ Z ↦ k x) (IsOpenImmersion.lift_fac j f h)
    -- Local instance justification (proof-local temporary data): the stalk transport along the point equality is used only to infer that the displayed composite is an isomorphism.
    haveI :
        IsIso ((Z.presheaf.stalkCongr
          (.of_eq hx)).hom) := by
      infer_instance
    exact IsIso.comp_isIso
  exact IsIso.of_isIso_comp_left
    (j.stalkMap ((IsOpenImmersion.lift j f h) x))
    ((IsOpenImmersion.lift j f h).stalkMap x)

end AlgebraicGeometry.IsOpenImmersion
