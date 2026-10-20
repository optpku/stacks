module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Coherence.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computations for mapped cospan coherence

This leaf contains the component readouts for the identity and composition comparison
isomorphisms.  Construction-only consumers can remain at `Coherence.Construction`.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.CospanTransform

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']
variable {x y z x' y' z' x'' y'' z'' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}
variable {f'' : x'' ⟶ z''} {g'' : y'' ⟶ z''}

/-- The forward left component of `map.idIso` is the ambient identity comparison. -/
@[simp]
theorem map.idIso.hom.left (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    Hom.left (map.idIso f g P).hom = (P.mapId x).hom := sorry

/-- The forward right component of `map.idIso` is the ambient identity comparison. -/
@[simp]
theorem map.idIso.hom.right (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    Hom.right (map.idIso f g P).hom = (P.mapId y).hom := sorry

/-- The forward base component of `map.idIso` is the ambient identity comparison. -/
@[simp]
theorem map.idIso.hom.base (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    Hom.base (map.idIso f g P).hom = (P.mapId z).hom := sorry

/-- The inverse left component of `map.idIso` is the inverse ambient identity comparison. -/
@[simp]
theorem map.idIso.inv.left (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    Hom.left (map.idIso f g P).inv = (P.mapId x).inv := sorry

/-- The inverse right component of `map.idIso` is the inverse ambient identity comparison. -/
@[simp]
theorem map.idIso.inv.right (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    Hom.right (map.idIso f g P).inv = (P.mapId y).inv := sorry

/-- The inverse base component of `map.idIso` is the inverse ambient identity comparison. -/
@[simp]
theorem map.idIso.inv.base (f : x ⟶ z) (g : y ⟶ z) (P : B ⥤ᵖ B') :
    Hom.base (map.idIso f g P).inv = (P.mapId z).inv := sorry

/-- The forward left component of `map.compIso` is the ambient composition comparison. -/
@[simp]
theorem map.compIso.hom.left
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    Hom.left (map.compIso ψ φ P).hom =
      (P.mapComp ψ.left φ.left).hom := sorry

/-- The forward right component of `map.compIso` is the ambient composition comparison. -/
@[simp]
theorem map.compIso.hom.right
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    Hom.right (map.compIso ψ φ P).hom =
      (P.mapComp ψ.right φ.right).hom := sorry

/-- The forward base component of `map.compIso` is the ambient composition comparison. -/
@[simp]
theorem map.compIso.hom.base
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    Hom.base (map.compIso ψ φ P).hom =
      (P.mapComp ψ.base φ.base).hom := sorry

/-- The inverse left component of `map.compIso` is the inverse ambient composition
comparison. -/
@[simp]
theorem map.compIso.inv.left
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    Hom.left (map.compIso ψ φ P).inv =
      (P.mapComp ψ.left φ.left).inv := sorry

/-- The inverse right component of `map.compIso` is the inverse ambient composition
comparison. -/
@[simp]
theorem map.compIso.inv.right
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    Hom.right (map.compIso ψ φ P).inv =
      (P.mapComp ψ.right φ.right).inv := sorry

/-- The inverse base component of `map.compIso` is the inverse ambient composition
comparison. -/
@[simp]
theorem map.compIso.inv.base
    (ψ : CospanTransform f g f' g')
    (φ : CospanTransform f' g' f'' g'') (P : B ⥤ᵖ B') :
    Hom.base (map.compIso ψ φ P).inv =
      (P.mapComp ψ.base φ.base).inv := sorry

end CategoryTheory.Bicategory.CospanTransform
