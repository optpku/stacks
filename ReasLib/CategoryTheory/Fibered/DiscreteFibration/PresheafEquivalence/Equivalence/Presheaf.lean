module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.ToPresheaf

/-!
# Presheaf-side Grothendieck comparison

This leaf owns the explicit comparison `ofPresheaf ⋙ toPresheaf ≅ 𝟭`, its componentwise
fiber-value equivalences, and their naturality.
-/

@[expose] public section

universe w u v

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

/-- The canonical fiber-value equivalences commute with restriction in the base. This is the
componentwise naturality needed to identify straightening after the discrete Grothendieck
construction with the original presheaf. -/
theorem ofPresheaf.fiberEquiv.naturality
    (F : Cᵒᵖ ⥤ Type (max w u)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    ((toPresheaf C).obj ((ofPresheaf C).obj F)).map f ≫
        (Equiv.toIso (ofPresheaf.fiberEquiv F (unop V))).hom =
      (Equiv.toIso (ofPresheaf.fiberEquiv F (unop U))).hom ≫ F.map f := sorry

namespace PresheafEquivalence

/-- Objectwise comparison `toPresheaf (ofPresheaf F) ≅ F`, assembled from the explicit
standard-fiber equivalences. -/
@[stacks 02Y2 "presheaf-side object comparison"]
noncomputable def toObjIso
    (F : Cᵒᵖ ⥤ Type (max w u)) :
    (toPresheaf C).obj ((ofPresheaf C).obj F) ≅ F :=
  NatIso.ofComponents
    (fun U => Equiv.toIso (ofPresheaf.fiberEquiv F (unop U)))
    (fun f => ofPresheaf.fiberEquiv.naturality F f)

/- Axiom audit: every component function of `PresheafEquivalence.toObjIso` is the explicit
`ofPresheaf.fiberEquiv`. Its `sorryAx` dependency is confined to inverse laws and naturality. -/

namespace toObjIso

/-- The forward component of `PresheafEquivalence.toObjIso` is the canonical fiber-value
equivalence. -/
@[simp]
theorem hom.app
    (F : Cᵒᵖ ⥤ Type (max w u)) (U : Cᵒᵖ) :
    (toObjIso F).hom.app U =
      (Equiv.toIso (ofPresheaf.fiberEquiv F (unop U))).hom := sorry

/-- The inverse component of `PresheafEquivalence.toObjIso` is the tautological value-to-fiber
map. -/
@[simp]
theorem inv.app
    (F : Cᵒᵖ ⥤ Type (max w u)) (U : Cᵒᵖ) :
    (toObjIso F).inv.app U =
      (Equiv.toIso (ofPresheaf.fiberEquiv F (unop U))).inv := sorry

/-- The objectwise comparisons `PresheafEquivalence.toObjIso` are natural in presheaf
morphisms. -/
theorem naturality
    {F G : Cᵒᵖ ⥤ Type (max w u)} (α : F ⟶ G) :
    ((ofPresheaf C ⋙ toPresheaf C).map α) ≫ (toObjIso G).hom =
      (toObjIso F).hom ≫ α := sorry

end toObjIso

variable (C) in
/-- The canonical comparison `ofPresheaf ⋙ toPresheaf ≅ 𝟭` on the size-stable presheaf
category. Its component functions are explicit and compute through `ofPresheaf.fiberEquiv`. The
base category is explicit because this global comparison has no value input from which Lean can
recover it. -/
@[stacks 02Y2 "presheaf-side Grothendieck comparison"]
noncomputable def ofIso :
    (ofPresheaf C ⋙ toPresheaf C :
      (Cᵒᵖ ⥤ Type (max w u)) ⥤ (Cᵒᵖ ⥤ Type (max w u))) ≅
      𝟭 (Cᵒᵖ ⥤ Type (max w u)) :=
  NatIso.ofComponents
    (fun F => toObjIso F)
    (fun α => toObjIso.naturality α)

/- Axiom audit: the comparison's non-`Prop` component data are the explicit fiber-value
equivalences above. Deferred axioms occur only in their inverse and naturality laws. -/

namespace ofIso

/-- The forward component of `PresheafEquivalence.ofIso` is
`PresheafEquivalence.toObjIso`. -/
@[simp]
theorem hom.app
    (F : Cᵒᵖ ⥤ Type (max w u)) :
    (ofIso C).hom.app F = (toObjIso F).hom := sorry

/-- The inverse component of `PresheafEquivalence.ofIso` is the inverse fiber-value
comparison. -/
@[simp]
theorem inv.app
    (F : Cᵒᵖ ⥤ Type (max w u)) :
    (ofIso C).inv.app F = (toObjIso F).inv := sorry

end ofIso

end PresheafEquivalence

end FiberedCategoryOver.Sets

end CategoryTheory
