/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CategoryOver.Cleavage
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Morphism.Reindex
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.LocallySurjective
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence

/-!
# Local properties of morphisms of fibred categories

This module exposes fixed-universe presentations of site-local properties owned by
`CartesianBasedFunctor`: local essential surjectivity on fiber objects and local lifting of fiber
morphisms. The explicit essential-image sieve and cover below are readouts in the established
fibred-category notation.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped CategoryTheory.Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- The fixed-universe view of the heterogeneous essential-preimage condition. -/
abbrev EssentialImage.HasPreimage
    (F : X ⟶ Y) {U V : C} (y : Y.p.Fiber U) (f : V ⟶ U) : Prop :=
  CartesianBasedFunctor.EssentialImage.HasPreimage
    (FiberedCategoryOver.toCartesianBasedFunctor F) y f

/-- Having an essential preimage is stable under further base change. -/
theorem EssentialImage.HasPreimage.precomp
    (F : X ⟶ Y) {U V W : C} {y : Y.p.Fiber U} {f : V ⟶ U}
    (h : EssentialImage.HasPreimage F y f) (g : W ⟶ V) :
    EssentialImage.HasPreimage F y (g ≫ f) := sorry

/-- The fixed-universe view of the heterogeneous essential-image sieve. -/
abbrev EssentialImage.sieve (F : X ⟶ Y) {U : C} (y : Y.p.Fiber U) : Sieve U :=
  CartesianBasedFunctor.EssentialImage.sieve
    (FiberedCategoryOver.toCartesianBasedFunctor F) y

/-- Membership in the essential-image sieve is the existence of a source-fiber model after
the indicated base change. -/
@[simp]
theorem EssentialImage.mem_sieve_iff
    (F : X ⟶ Y) {U V : C} (y : Y.p.Fiber U) (f : V ⟶ U) :
    EssentialImage.sieve F y f ↔ EssentialImage.HasPreimage F y f := sorry

/-- The fixed-universe view of heterogeneous local essential surjectivity. -/
abbrev LocallyEssentiallySurjective
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.LocallyEssentiallySurjective J
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- The canonical sieve formulation is equivalent to the coverwise source presentation used in
the textbook definition. -/
theorem LocallyEssentiallySurjective.iff_forall_cover
    {J : GrothendieckTopology C} {F : X ⟶ Y} :
    LocallyEssentiallySurjective J F ↔
      ∀ {U : C} (y : Y.p.Fiber U), ∃ S : J.Cover U, ∀ I : S.Arrow,
        EssentialImage.HasPreimage F y I.f := sorry

/-- Local essential surjectivity is equivalent to the essential-image sieve of every target
fiber object being covering. -/
theorem LocallyEssentiallySurjective.iff_forall_mem
    {J : GrothendieckTopology C} {F : X ⟶ Y} :
    LocallyEssentiallySurjective J F ↔
      ∀ {U : C} (y : Y.p.Fiber U), EssentialImage.sieve F y ∈ J U := sorry

/-- Under local essential surjectivity, the essential-image sieve of a target-fiber object is
covering. -/
theorem LocallyEssentiallySurjective.sieve_mem
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : LocallyEssentiallySurjective J F)
    {U : C} (y : Y.p.Fiber U) :
    EssentialImage.sieve F y ∈ J U := sorry

/-- The fixed-universe view of the canonical heterogeneous essential-image cover. -/
abbrev EssentialImage.cover
    {J : GrothendieckTopology C} (F : X ⟶ Y)
    (hF : LocallyEssentiallySurjective J F)
    {U : C} (y : Y.p.Fiber U) : J.Cover U :=
  CartesianBasedFunctor.EssentialImage.cover
    (FiberedCategoryOver.toCartesianBasedFunctor F) hF y

/-- Every arrow in the canonical essential-image cover admits a source-fiber model of the
corresponding reindexed target object. -/
theorem EssentialImage.cover_spec
    {J : GrothendieckTopology C} (F : X ⟶ Y)
    (hF : LocallyEssentiallySurjective J F)
    {U : C} (y : Y.p.Fiber U) (I : (EssentialImage.cover F hF y).Arrow) :
    ∃ x : X.p.Fiber I.Y,
      Nonempty ((FiberedCategoryOver.fiberFunctor F I.Y).obj x ≅
        I.f⁎[Y.chosenCleavage] y) := sorry

/-- Local essential surjectivity on fiber objects is stable under composition of morphisms of
fibered categories. -/
theorem LocallyEssentiallySurjective.comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : LocallyEssentiallySurjective J F)
    (hG : LocallyEssentiallySurjective J G) :
    LocallyEssentiallySurjective J (F ≫ G) := sorry

/-- An equivalence over the base is locally essentially surjective on fiber objects. -/
theorem LocallyEssentiallySurjective.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    LocallyEssentiallySurjective J F := sorry

/-- Precomposition by an equivalence over the base preserves local essential surjectivity. -/
theorem LocallyEssentiallySurjective.comp_left_of_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} (E : X ⟶ Y)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (G : Y ⟶ Z) (hG : LocallyEssentiallySurjective J G) :
    LocallyEssentiallySurjective J (E ≫ G) := sorry

/-- Postcomposition by an equivalence over the base preserves local essential surjectivity. -/
theorem LocallyEssentiallySurjective.comp_right_of_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} (F : X ⟶ Y)
    (hF : LocallyEssentiallySurjective J F) (E : Y ⟶ Z)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence) :
    LocallyEssentiallySurjective J (F ≫ E) := sorry

/-- Local essential surjectivity reflects across postcomposition by an equivalence over the
base. -/
theorem LocallyEssentiallySurjective.of_comp_right_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} (F : X ⟶ Y) (E : Y ⟶ Z)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (hFE : LocallyEssentiallySurjective J (F ≫ E)) :
    LocallyEssentiallySurjective J F := sorry

/-- Transport local essential surjectivity along an isomorphism of parallel
morphisms of fibered categories. -/
theorem LocallyEssentiallySurjective.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : LocallyEssentiallySurjective J F) :
    LocallyEssentiallySurjective J G := sorry

/-- Parallel isomorphic morphisms of fibered categories are locally
essentially surjective simultaneously. -/
theorem LocallyEssentiallySurjective.iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    LocallyEssentiallySurjective J F ↔ LocallyEssentiallySurjective J G := sorry

/-- If a composite is locally essentially surjective, then so is its right
factor. -/
theorem LocallyEssentiallySurjective.right_of_comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (h : LocallyEssentiallySurjective J (F ≫ G)) :
    LocallyEssentiallySurjective J G := sorry

/-- A right factor is locally essentially surjective when its composite is
isomorphic to a locally essentially surjective morphism. -/
theorem LocallyEssentiallySurjective.right_of_comp_iso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    {H : X ⟶ Z} (e : F ≫ G ≅ H)
    (hH : LocallyEssentiallySurjective J H) :
    LocallyEssentiallySurjective J G := sorry

/-- A morphism of fibred categories locally lifts fiber morphisms when its canonical
Hom-presheaf maps are locally surjective on every slice site. -/
abbrev LocallyLifts
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  Homwise.IsLocallySurjective J F

/-- The source-facing local lifting condition is exactly homwise local surjectivity of the
canonical Hom-presheaf maps. -/
theorem LocallyLifts.iff_homwise
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    LocallyLifts J F ↔ Homwise.IsLocallySurjective J F := sorry

/-- The canonical Hom-presheaf formulation of `LocallyLifts` is equivalent to the coverwise
lifting condition expressed using chosen reindexing. -/
theorem LocallyLifts.iff_forall_cover
    {J : GrothendieckTopology C} {F : X ⟶ Y} :
    LocallyLifts J F ↔
      ∀ {U : C} (x x' : X.p.Fiber U)
        (b : (FiberedCategoryOver.fiberFunctor F U).obj x ⟶
          (FiberedCategoryOver.fiberFunctor F U).obj x'),
        ∃ S : J.Cover U, ∀ I : S.Arrow,
          ∃ a :
            I.f⁎[X.chosenCleavage] x ⟶
              I.f⁎[X.chosenCleavage] x',
            CommSq
              ((Y.chosenCleavage.reindex I.f).map b)
              (FiberedCategoryOver.Reindex.mapIso F I.f x).hom
              (FiberedCategoryOver.Reindex.mapIso F I.f x').hom
              ((FiberedCategoryOver.fiberFunctor F I.Y).map a) := sorry

/-- Local lifting of fiber morphisms is stable under composition. -/
theorem LocallyLifts.comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : LocallyLifts J F) (hG : LocallyLifts J G) :
    LocallyLifts J (F ≫ G) := sorry

/-- An equivalence over the base locally lifts fiber morphisms. -/
theorem LocallyLifts.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    LocallyLifts J F := sorry

/-- Transport local lifting of fiber morphisms along an isomorphism of parallel morphisms. -/
theorem LocallyLifts.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : LocallyLifts J F) :
    LocallyLifts J G := sorry

/-- Parallel isomorphic morphisms locally lift fiber morphisms simultaneously. -/
theorem LocallyLifts.iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    LocallyLifts J F ↔ LocallyLifts J G := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
