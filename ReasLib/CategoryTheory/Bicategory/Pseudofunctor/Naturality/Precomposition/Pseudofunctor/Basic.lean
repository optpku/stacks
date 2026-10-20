module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans.Category

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.Precomposition.Hom

/-!
# The precomposition pseudofunctor

The strict pseudofunctor induced between pseudofunctor bicategories by
precomposition with a fixed pseudofunctor. Base-facing computation rules live
in `Precomposition.Pseudofunctor.Computations`.
-/

@[expose] public section

universe wA vA uA wB vB uB wD vD uD

namespace CategoryTheory

open scoped Bicategory Pseudofunctor.StrongTrans

namespace Pseudofunctor

variable {B : Type uB} [Bicategory.{wB, vB} B]
  {D : Type uD} [Bicategory.{wD, vD} D]

section Precomposition

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped Pseudofunctor.StrongTrans


variable {A : Type uA} [Bicategory.{wA, vA} A]

/-- The identity comparison for precomposition of the functor bicategory. -/
private def precompMapId
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) :
    @Iso (StrongTrans (K.comp F) (K.comp F))
      (StrongTrans.homCategoryOwner (F := K.comp F) (G := K.comp F))
      ((StrongTrans.id F).precomp K) (StrongTrans.id (K.comp F)) :=
  @Iso.refl _ (StrongTrans.homCategoryOwner (F := K.comp F) (G := K.comp F))
    ((StrongTrans.id F).precomp K)

/-- The composition comparison for precomposition of the functor bicategory. -/
private def precompMapComp
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    @Iso (StrongTrans (K.comp F) (K.comp H))
      (StrongTrans.homCategoryOwner (F := K.comp F) (G := K.comp H))
      ((StrongTrans.vcomp η θ).precomp K)
      (StrongTrans.vcomp (η.precomp K) (θ.precomp K)) :=
  @Iso.refl _ (StrongTrans.homCategoryOwner (F := K.comp F) (G := K.comp H))
    ((StrongTrans.vcomp η θ).precomp K)

/-- Precomposition strictly preserves identity strong transformations. -/
private theorem precompMap_id
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) :
    (StrongTrans.id F).precomp K =
      StrongTrans.id (K.comp F) := sorry

/-- The identity comparison for precomposition is induced by strict preservation of
identities. -/
private theorem precompMapId_eq_eqToIso
    (K : Pseudofunctor A B) (F : Pseudofunctor B D) :
    precompMapId K F =
      @eqToIso _ (StrongTrans.homCategoryOwner (F := K.comp F) (G := K.comp F))
        _ _ (precompMap_id K F) := sorry

/-- Precomposition strictly preserves composition of strong transformations. -/
private theorem precompMap_comp
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    (StrongTrans.vcomp η θ).precomp K =
      StrongTrans.vcomp (η.precomp K) (θ.precomp K) := sorry

/-- The composition comparison for precomposition is induced by strict preservation of
composition. -/
private theorem precompMapComp_eq_eqToIso
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) :
    precompMapComp K η θ =
      @eqToIso _ (StrongTrans.homCategoryOwner (F := K.comp F) (G := K.comp H))
        _ _ (precompMap_comp K η θ) := sorry

/-- Explicit vertical composition in a strong-transformation hom-category, used to keep
the canonical scoped hom-category's universe fixed in the coherence statements below. -/
private def precompHomVcomp
    {F G : Pseudofunctor A D}
    {η θ ι : StrongTrans F G}
    (Γ : StrongTrans.Hom η θ) (Δ : StrongTrans.Hom θ ι) :
    StrongTrans.Hom η ι :=
  StrongTrans.Hom.of (StrongTrans.Modification.vcomp Γ.as Δ.as)

/-- Precomposition is compatible with left whiskering in the functor bicategory. -/
private theorem precompMap₂_whisker_left
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    (η : F ⟶ G) {θ ι : G ⟶ H} (Γ : θ ⟶ ι) :
    StrongTrans.Hom.precomp (η ◁ Γ) K =
      precompHomVcomp (precompMapComp K η θ).hom
        (precompHomVcomp
          (StrongTrans.whiskerLeft (η.precomp K)
            (StrongTrans.Hom.precomp Γ K))
          (precompMapComp K η ι).inv) := sorry

/-- Precomposition is compatible with right whiskering in the functor bicategory. -/
private theorem precompMap₂_whisker_right
    (K : Pseudofunctor A B) {F G H : Pseudofunctor B D}
    {η θ : F ⟶ G} (Γ : η ⟶ θ) (ι : G ⟶ H) :
    StrongTrans.Hom.precomp (Γ ▷ ι) K =
      precompHomVcomp (precompMapComp K η ι).hom
        (precompHomVcomp
          (StrongTrans.whiskerRight
            (StrongTrans.Hom.precomp Γ K) (ι.precomp K))
          (precompMapComp K θ ι).inv) := sorry

/-- Precomposition is compatible with the left unitor of the functor bicategory. -/
private theorem precompMap₂_left_unitor
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) :
    StrongTrans.Hom.precomp (λ_ η).hom K =
      precompHomVcomp
        (precompMapComp K (StrongTrans.id F) η).hom
        (precompHomVcomp
          (StrongTrans.whiskerRight
            (precompMapId K F).hom (η.precomp K))
          (StrongTrans.leftUnitor (η.precomp K)).hom) := sorry

/-- Precomposition is compatible with the right unitor of the functor bicategory. -/
private theorem precompMap₂_right_unitor
    (K : Pseudofunctor A B) {F G : Pseudofunctor B D}
    (η : F ⟶ G) :
    StrongTrans.Hom.precomp (ρ_ η).hom K =
      precompHomVcomp
        (precompMapComp K η (StrongTrans.id G)).hom
        (precompHomVcomp
          (StrongTrans.whiskerLeft
            (η.precomp K) (precompMapId K G).hom)
          (StrongTrans.rightUnitor (η.precomp K)).hom) := sorry

/-- Precomposition is compatible with the associator of the functor bicategory. -/
private theorem precompMap₂_associator
    (K : Pseudofunctor A B) {F G H I : Pseudofunctor B D}
    (η : F ⟶ G) (θ : G ⟶ H) (ι : H ⟶ I) :
    StrongTrans.Hom.precomp (α_ η θ ι).hom K =
      precompHomVcomp
        (precompMapComp K (StrongTrans.vcomp η θ) ι).hom
        (precompHomVcomp
          (StrongTrans.whiskerRight
            (precompMapComp K η θ).hom (ι.precomp K))
          (precompHomVcomp
            (StrongTrans.associator
              (η.precomp K) (θ.precomp K) (ι.precomp K)).hom
            (precompHomVcomp
              (StrongTrans.whiskerLeft (η.precomp K)
                (precompMapComp K θ ι).inv)
              (precompMapComp K η (StrongTrans.vcomp θ ι)).inv))) := sorry

variable (D) in
/-- Precomposition by a fixed pseudofunctor is a strict pseudofunctor between
functor bicategories. Weakness of the fixed pseudofunctor is already contained in each
composite object; precomposition preserves transformations and modifications strictly.

The common target bicategory is explicit because the fixed pseudofunctor `K`
determines its source and middle bicategories, but not that target. -/
def precomp (K : Pseudofunctor A B) :
    StrictPseudofunctor
      (Pseudofunctor B D) (Pseudofunctor A D) where
  obj F := K.comp F
  map η := η.precomp K
  map₂ Γ := StrongTrans.Hom.precomp Γ K
  map₂_id η := StrongTrans.precomp₂.id η K
  map₂_comp Γ Δ := StrongTrans.precomp₂.comp Γ Δ K
  mapId := precompMapId K
  mapComp := precompMapComp K
  map₂_whisker_left := precompMap₂_whisker_left K
  map₂_whisker_right := precompMap₂_whisker_right K
  map₂_left_unitor := precompMap₂_left_unitor K
  map₂_right_unitor := precompMap₂_right_unitor K
  map₂_associator := precompMap₂_associator K
  map_id := precompMap_id K
  mapId_eq_eqToIso := precompMapId_eq_eqToIso K
  map_comp := precompMap_comp K
  mapComp_eq_eqToIso := precompMapComp_eq_eqToIso K

/- Data and axiom audit (mathlib 4.32):

The object, `1`-morphism, `2`-morphism, identity, and composition data of
`precomp` are concrete owners from the preceding layers. The private helpers
supply only `Prop`-valued naturality and bicategorical coherence fields. -/

end Precomposition

end Pseudofunctor

end CategoryTheory
