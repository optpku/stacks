/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocalProperties
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of induced bicategories

This module packages the hom-wise equivalence and groupoid facts of an induced
bicategory.  It does not depend on an object property or a full-subbicategory
presentation.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open scoped Bicategory

universe w v u u'

namespace Bicategory.InducedBicategory

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable {B : Type u'} {D : Type u} [Bicategory.{w, v} D] {F : B → D}

/-- Lifting preserves identity `2`-morphisms. -/
private theorem liftMapFunctor.map_id (X Y : InducedBicategory D F) (f : F X ⟶ F Y) :
    mkHom₂ (𝟙 f) = 𝟙 (mkHom f) := sorry

/-- Lifting preserves composition of `2`-morphisms. -/
private theorem liftMapFunctor.map_comp (X Y : InducedBicategory D F)
    {f g h : F X ⟶ F Y} (η : f ⟶ g) (θ : g ⟶ h) :
    mkHom₂ (η ≫ θ) = mkHom₂ η ≫ mkHom₂ θ := sorry

/-- Lift ambient `1`- and `2`-morphisms to the hom-category of an induced bicategory. This is
the data-preserving inverse to `forget.mapFunctor X Y`: both object and morphism maps are the
corresponding induced-bicategory constructors. -/
@[stacks 0040 "lift to an induced-bicategory Hom category"]
def liftMapFunctor (X Y : InducedBicategory D F) :
    (F X ⟶ F Y) ⥤ (X ⟶ Y) where
  obj f := mkHom f
  map η := mkHom₂ η
  map_id f := liftMapFunctor.map_id X Y f
  map_comp η θ := liftMapFunctor.map_comp X Y η θ

/-- Naturality of the identity comparison after lifting and forgetting ambient morphisms. -/
private theorem liftForgetIso.naturality (X Y : InducedBicategory D F) :
    ∀ {f g : F X ⟶ F Y} (η : f ⟶ g),
      (liftMapFunctor X Y ⋙ forget.mapFunctor X Y).map η ≫ (Iso.refl g).hom =
        (Iso.refl f).hom ≫ (𝟭 (F X ⟶ F Y)).map η := sorry

/-- Lifting and then forgetting is naturally the identity on the ambient hom-category. -/
private def liftForgetIso (X Y : InducedBicategory D F) :
    liftMapFunctor X Y ⋙ forget.mapFunctor X Y ≅ 𝟭 _ :=
  NatIso.ofComponents (fun f => Iso.refl f) (liftForgetIso.naturality X Y)

/-- Naturality of the identity comparison after forgetting and lifting induced morphisms. -/
private theorem forgetLiftIso.naturality (X Y : InducedBicategory D F) :
    ∀ {f g : X ⟶ Y} (η : f ⟶ g),
      (forget.mapFunctor X Y ⋙ liftMapFunctor X Y).map η ≫ (Iso.refl g).hom =
        (Iso.refl f).hom ≫ (𝟭 (X ⟶ Y)).map η := sorry

/-- Forgetting and then lifting is naturally the identity on the induced hom-category. -/
private def forgetLiftIso (X Y : InducedBicategory D F) :
    forget.mapFunctor X Y ⋙ liftMapFunctor X Y ≅ 𝟭 _ :=
  NatIso.ofComponents (fun f => Iso.refl f) (forgetLiftIso.naturality X Y)

/-- The canonical equivalence between an ambient hom-category and the corresponding hom-category
of an induced bicategory. Both functors preserve the underlying `1`- and `2`-morphisms
definitionally. -/
@[stacks 0040 "hom-category equivalence for an induced bicategory"]
def homEquivalence (X Y : InducedBicategory D F) :
    (F X ⟶ F Y) ≌ (X ⟶ Y) :=
  CategoryTheory.Equivalence.mk (liftMapFunctor X Y) (forget.mapFunctor X Y)
    (liftForgetIso X Y) (forgetLiftIso X Y)

namespace Implementation

/-- Mapping a lifted ambient `2`-morphism back along the forgetful hom functor recovers it. -/
private theorem forget.mapFunctor.map_preimage (X Y : InducedBicategory D F)
    {f g : X ⟶ Y}
    (η : (forget.mapFunctor X Y).obj f ⟶ (forget.mapFunctor X Y).obj g) :
    (forget.mapFunctor X Y).map (mkHom₂ η) = η := sorry
/- Proof strategy: apply `hom₂_ext`; the underlying ambient `2`-morphism of `mkHom₂ η` is
definitionally `η`. -/

/-- Lifting the image of an induced `2`-morphism recovers the original induced cell. -/
private theorem forget.mapFunctor.preimage_map (X Y : InducedBicategory D F)
    {f g : X ⟶ Y} (η : f ⟶ g) :
    mkHom₂ ((forget.mapFunctor X Y).map η) = η := sorry
/- Proof strategy: apply `hom₂_ext`; both sides have the same underlying ambient cell `η.hom`. -/

/-- The forgetful pseudofunctor from an induced bicategory is fully faithful on every hom
category. This is the canonical inverse-on-cells data missing from the base mathlib file. -/
private def forget.mapFunctor.fullyFaithful (X Y : InducedBicategory D F) :
    (forget.mapFunctor X Y).FullyFaithful where
  preimage η := mkHom₂ η
  map_preimage := forget.mapFunctor.map_preimage X Y
  preimage_map := forget.mapFunctor.preimage_map X Y

end Implementation

/-- The forgetful pseudofunctor from an induced bicategory is an equivalence on every hom
category. -/
@[stacks 0040 "induced-bicategory forgetful Hom equivalence"]
instance forget.mapFunctor.isEquivalence (X Y : InducedBicategory D F) :
    (forget.mapFunctor X Y).IsEquivalence := sorry
/- Proof strategy: construct `Functor.IsEquivalence` directly. Fill `faithful` and `full` with
the corresponding fields of
`Implementation.forget.mapFunctor.fullyFaithful X Y`; fill `essSurj` by sending an
ambient `1`-morphism `f : F X ⟶ F Y` to the exact preimage `mkHom f`. The class then supplies
the derived `Faithful`, `Full`, and `EssSurj` instances without three duplicate owners. -/

/-- The forgetful pseudofunctor from an induced bicategory is locally an equivalence. -/
@[stacks 0040 "induced-bicategory forgetful local equivalence"]
instance forget.isLocallyEquivalence :
    (forget : StrictPseudofunctor
      (InducedBicategory D F) D).toPseudofunctor.IsLocallyEquivalence := sorry
/- Proof strategy: at each pair of objects, use `forget.mapFunctor.isEquivalence`. -/

/-- Each hom-category of an induced bicategory inherits groupoidality from the corresponding
ambient hom-category. This pointwise instance is more reusable than assuming that the whole
ambient bicategory is locally groupoidal. -/
@[stacks 0040 "groupoidal Hom categories for induced bicategories"]
instance homGroupoid (X Y : InducedBicategory D F) [IsGroupoid (F X ⟶ F Y)] :
    IsGroupoid (X ⟶ Y) := sorry
/- Proof strategy: lift `asIso η.hom` with `InducedBicategory.isoMk`; its forward cell is `η` by
`hom₂_ext`, so the canonical `IsIso` instance transports through the hom wrapper. -/

/-- Each hom-category of an induced bicategory inherits thinness from the corresponding ambient
hom-category. This pointwise bridge lets nested full subbicategories reuse a single thinness
owner instead of rebuilding uniqueness of `2`-morphisms at every layer. -/
@[stacks 0040 "thin Hom categories for induced bicategories"]
instance homIsThin (X Y : InducedBicategory D F) [Quiver.IsThin (F X ⟶ F Y)] :
    Quiver.IsThin (X ⟶ Y) := sorry

end Bicategory.InducedBicategory

end CategoryTheory
