/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Fiber.Hom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms in a fiber

The standard fiber inclusion preserves and reflects invertibility.  The
reflection direction uses that the inverse of a vertical isomorphism is again
vertical.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory.Functor.Fiber

variable {C : Type u} [Category.{v} C]
variable {S : Type uS} [Category.{vS} S]
variable {p : S ⥤ C} {U : C} {x y : p.Fiber U}

/-- The two ambient inverse maps of an isomorphism give the forward inverse law after they are
packaged as vertical morphisms in a standard fiber. -/
theorem isoMk.hom_inv_id (e : x.1 ≅ y.1)
    (hhom : p.IsHomLift (𝟙 U) e.hom) :
    Hom.mk e.hom hhom ≫
        Hom.mk e.inv (IsHomLift.lift_id_inv_of e hhom) = 𝟙 x := sorry

/-- The two ambient inverse maps of an isomorphism give the reverse inverse law after they are
packaged as vertical morphisms in a standard fiber. -/
theorem isoMk.inv_hom_id (e : x.1 ≅ y.1)
    (hhom : p.IsHomLift (𝟙 U) e.hom) :
    Hom.mk e.inv (IsHomLift.lift_id_inv_of e hhom) ≫
        Hom.mk e.hom hhom = 𝟙 y := sorry

/-- Package an ambient isomorphism whose forward map is vertical into an isomorphism in the
standard fiber. The inverse lift is derived, and the ambient isomorphism remains the sole
non-`Prop` data owner. -/
def isoMk (e : x.1 ≅ y.1)
    (hhom : p.IsHomLift (𝟙 U) e.hom) :
    x ≅ y where
  hom := Hom.mk e.hom hhom
  inv := Hom.mk e.inv (IsHomLift.lift_id_inv_of e hhom)
  hom_inv_id := isoMk.hom_inv_id e hhom
  inv_hom_id := isoMk.inv_hom_id e hhom

/-- The forward map of `isoMk` is the supplied ambient isomorphism map after inclusion into the
standard fiber. -/
@[simp]
theorem isoMk.hom.val (e : x.1 ≅ y.1)
    (hhom : p.IsHomLift (𝟙 U) e.hom) :
    (fiberInclusion (p := p) (S := U)).map (isoMk e hhom).hom = e.hom := sorry

/-- The inverse map of `isoMk` is the supplied ambient inverse after inclusion into the standard
fiber. -/
@[simp]
theorem isoMk.inv.val (e : x.1 ≅ y.1)
    (hhom : p.IsHomLift (𝟙 U) e.hom) :
    (fiberInclusion (p := p) (S := U)).map (isoMk e hhom).inv = e.inv := sorry

/-- A morphism in a standard fiber is invertible exactly when its underlying
morphism in the total category is invertible. -/
theorem isIso_iff_val {x y : p.Fiber U} (f : x ⟶ y) :
    IsIso f ↔ IsIso f.1 := sorry

/- Data audit: `isoMk` stores exactly the supplied ambient isomorphism. Its inverse arrow is the
ambient inverse, while verticality and the two inverse laws are confined to proof fields. -/

end CategoryTheory.Functor.Fiber
