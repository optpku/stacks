/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparing fixed-target family models

The indexed model `SemiRepresentableFamily.Over X` and the formal-coproduct
model `SemiRepresentableFamily.OverFamily X` have the same objects and
morphisms with different field names. Concrete functors in both directions are
mutually inverse up to natural isomorphism.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C] {X : C}

namespace Over

/-- Regard an indexed fixed-target family as a formal coproduct in `C / X`. -/
@[stacks 01G0 "site family to formal-coproduct family"]
def toOverFamilyObj (K : Over.{w} X) : OverFamily.{v, u, w} X where
  I := K.index
  obj := K.obj

/-- Map an indexed-family morphism to the corresponding formal-coproduct morphism. -/
def toOverFamilyMap {K L : Over.{w} X} (f : K ⟶ L) :
    toOverFamilyObj K ⟶ toOverFamilyObj L where
  f := f.α
  φ := f.f

/-- The formal-coproduct comparison preserves identity morphisms. -/
theorem toOverFamilyMap_id (K : Over.{w} X) :
    toOverFamilyMap (𝟙 K) = 𝟙 (toOverFamilyObj K) := sorry

/-- The formal-coproduct comparison preserves composition. -/
theorem toOverFamilyMap_comp {K L M : Over.{w} X} (f : K ⟶ L) (g : L ⟶ M) :
    toOverFamilyMap (f ≫ g) = toOverFamilyMap f ≫ toOverFamilyMap g := sorry

/-- The functor from indexed fixed-target families to formal-coproduct families. -/
@[stacks 01G0 "fixed-target family comparison functor"]
def toOverFamily : Over.{w} X ⥤ OverFamily.{v, u, w} X where
  obj := toOverFamilyObj
  map := toOverFamilyMap
  map_id := toOverFamilyMap_id
  map_comp := toOverFamilyMap_comp

end Over

namespace OverFamily

/-- Forget the formal-coproduct packaging of a fixed-target family. -/
def toIndexedFamilyObj (K : OverFamily.{v, u, w} X) : Over.{w} X where
  index := K.index
  obj := K.obj

/-- Forget the formal-coproduct packaging of a fixed-target family morphism. -/
def toIndexedFamilyMap {K L : OverFamily.{v, u, w} X} (f : K ⟶ L) :
    toIndexedFamilyObj K ⟶ toIndexedFamilyObj L where
  α := f.f
  f := f.φ

/-- Forgetting formal-coproduct packaging preserves identity morphisms. -/
theorem toIndexedFamilyMap_id (K : OverFamily.{v, u, w} X) :
    toIndexedFamilyMap (𝟙 K) = 𝟙 (toIndexedFamilyObj K) := sorry

/-- Forgetting formal-coproduct packaging preserves composition. -/
theorem toIndexedFamilyMap_comp {K L M : OverFamily.{v, u, w} X}
    (f : K ⟶ L) (g : L ⟶ M) :
    toIndexedFamilyMap (f ≫ g) = toIndexedFamilyMap f ≫ toIndexedFamilyMap g := sorry

/-- The functor from formal-coproduct families to indexed fixed-target families. -/
def toIndexedFamily : OverFamily.{v, u, w} X ⥤ Over.{w} X where
  obj := toIndexedFamilyObj
  map := toIndexedFamilyMap
  map_id := toIndexedFamilyMap_id
  map_comp := toIndexedFamilyMap_comp

end OverFamily

namespace Over.toOverFamily

/-- The forward component of the indexed-family round-trip comparison. -/
def roundTripHom (K : Over.{w} X) :
    (Over.toOverFamily ⋙ OverFamily.toIndexedFamily).obj K ⟶ K :=
  { α := id, f := fun _ ↦ 𝟙 _ }

/-- The inverse component of the indexed-family round-trip comparison. -/
def roundTripInv (K : Over.{w} X) :
    K ⟶ (Over.toOverFamily ⋙ OverFamily.toIndexedFamily).obj K :=
  { α := id, f := fun _ ↦ 𝟙 _ }

/-- The indexed-family round-trip comparison satisfies the forward inverse law. -/
theorem roundTrip_hom_inv_id (K : Over.{w} X) :
    roundTripHom K ≫ roundTripInv K = 𝟙 _ := sorry

/-- The indexed-family round-trip comparison satisfies the reverse inverse law. -/
theorem roundTrip_inv_hom_id (K : Over.{w} X) :
    roundTripInv K ≫ roundTripHom K = 𝟙 _ := sorry

/-- Component of the natural isomorphism from conversion through `OverFamily`
back to the original indexed family. -/
def roundTripIsoApp (K : Over.{w} X) :
    (Over.toOverFamily ⋙ OverFamily.toIndexedFamily).obj K ≅ K where
  hom := roundTripHom K
  inv := roundTripInv K
  hom_inv_id := roundTrip_hom_inv_id K
  inv_hom_id := roundTrip_inv_hom_id K

/-- The comparison isomorphisms are natural in indexed-family morphisms. -/
theorem roundTripIsoApp_naturality {K L : Over.{w} X} (f : K ⟶ L) :
    (Over.toOverFamily ⋙ OverFamily.toIndexedFamily).map f ≫
        (roundTripIsoApp L).hom =
      (roundTripIsoApp K).hom ≫ f := sorry

/-- Converting an indexed family to a formal-coproduct family and back is
naturally isomorphic to the identity. -/
@[stacks 01G0 "site-family comparison inverse"]
def roundTripIso :
    Over.toOverFamily ⋙ OverFamily.toIndexedFamily ≅ 𝟭 (Over.{w} X) :=
  NatIso.ofComponents roundTripIsoApp (fun f ↦ roundTripIsoApp_naturality f)

end Over.toOverFamily

namespace OverFamily.toIndexedFamily

/-- The forward component of the formal-coproduct-family round-trip comparison. -/
def roundTripHom (K : OverFamily.{v, u, w} X) :
    (OverFamily.toIndexedFamily ⋙ Over.toOverFamily).obj K ⟶ K :=
  { f := id, φ := fun _ ↦ 𝟙 _ }

/-- The inverse component of the formal-coproduct-family round-trip comparison. -/
def roundTripInv (K : OverFamily.{v, u, w} X) :
    K ⟶ (OverFamily.toIndexedFamily ⋙ Over.toOverFamily).obj K :=
  { f := id, φ := fun _ ↦ 𝟙 _ }

/-- The formal-coproduct-family round-trip comparison satisfies the forward inverse law. -/
theorem roundTrip_hom_inv_id (K : OverFamily.{v, u, w} X) :
    roundTripHom K ≫ roundTripInv K = 𝟙 _ := sorry

/-- The formal-coproduct-family round-trip comparison satisfies the reverse inverse law. -/
theorem roundTrip_inv_hom_id (K : OverFamily.{v, u, w} X) :
    roundTripInv K ≫ roundTripHom K = 𝟙 _ := sorry

/-- Component of the natural isomorphism from conversion through the indexed
model back to the original formal-coproduct family. -/
def roundTripIsoApp (K : OverFamily.{v, u, w} X) :
    (OverFamily.toIndexedFamily ⋙ Over.toOverFamily).obj K ≅ K where
  hom := roundTripHom K
  inv := roundTripInv K
  hom_inv_id := roundTrip_hom_inv_id K
  inv_hom_id := roundTrip_inv_hom_id K

/-- The comparison isomorphisms are natural in formal-coproduct family morphisms. -/
theorem roundTripIsoApp_naturality
    {K L : OverFamily.{v, u, w} X} (f : K ⟶ L) :
    (OverFamily.toIndexedFamily ⋙ Over.toOverFamily).map f ≫
        (roundTripIsoApp L).hom =
      (roundTripIsoApp K).hom ≫ f := sorry

/-- Converting a formal-coproduct family to an indexed family and back is
naturally isomorphic to the identity. -/
@[stacks 01G0 "formal-coproduct family comparison inverse"]
def roundTripIso :
    OverFamily.toIndexedFamily ⋙ Over.toOverFamily ≅
      𝟭 (OverFamily.{v, u, w} X) :=
  NatIso.ofComponents roundTripIsoApp (fun f ↦ roundTripIsoApp_naturality f)

end OverFamily.toIndexedFamily

end CategoryTheory.SemiRepresentableFamily
