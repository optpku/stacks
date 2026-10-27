/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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
    EssentialImage.HasPreimage F y (g ≫ f) := by
  rcases h with ⟨x, ⟨e⟩⟩
  refine ⟨g⁎[X.chosenCleavage] x, ⟨?_⟩⟩
  exact (FiberedCategoryOver.Reindex.mapIso F g x).symm ≪≫
    (Y.chosenCleavage.reindex g).mapIso e ≪≫
      (Functor.Cleavage.Reindex.compIsoApp Y.chosenCleavage f g y).symm

/-- The fixed-universe view of the heterogeneous essential-image sieve. -/
abbrev EssentialImage.sieve (F : X ⟶ Y) {U : C} (y : Y.p.Fiber U) : Sieve U :=
  CartesianBasedFunctor.EssentialImage.sieve
    (FiberedCategoryOver.toCartesianBasedFunctor F) y

/-- Membership in the essential-image sieve is the existence of a source-fiber model after
the indicated base change. -/
@[simp]
theorem EssentialImage.mem_sieve_iff
    (F : X ⟶ Y) {U V : C} (y : Y.p.Fiber U) (f : V ⟶ U) :
    EssentialImage.sieve F y f ↔ EssentialImage.HasPreimage F y f := Iff.rfl

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
        EssentialImage.HasPreimage F y I.f := by
  constructor
  · intro hF U y
    exact ⟨⟨EssentialImage.sieve F y, hF y⟩, fun I ↦ I.hf⟩
  · intro hF U y
    obtain ⟨S, hS⟩ := hF y
    exact J.superset_covering (fun V f hf ↦ hS ⟨V, f, hf⟩) S.condition

/-- Local essential surjectivity is equivalent to the essential-image sieve of every target
fiber object being covering. -/
theorem LocallyEssentiallySurjective.iff_forall_mem
    {J : GrothendieckTopology C} {F : X ⟶ Y} :
    LocallyEssentiallySurjective J F ↔
      ∀ {U : C} (y : Y.p.Fiber U), EssentialImage.sieve F y ∈ J U := Iff.rfl

/-- Under local essential surjectivity, the essential-image sieve of a target-fiber object is
covering. -/
theorem LocallyEssentiallySurjective.sieve_mem
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : LocallyEssentiallySurjective J F)
    {U : C} (y : Y.p.Fiber U) :
    EssentialImage.sieve F y ∈ J U := hF y

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
        I.f⁎[Y.chosenCleavage] y) := I.hf

/-- Local essential surjectivity on fiber objects is stable under composition of morphisms of
fibered categories. -/
theorem LocallyEssentiallySurjective.comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : LocallyEssentiallySurjective J F)
    (hG : LocallyEssentiallySurjective J G) :
    LocallyEssentiallySurjective J (F ≫ G) := by
  intro U z
  apply J.transitive (hG z) (EssentialImage.sieve (F ≫ G) z)
  intro V f hf
  rcases hf with ⟨y, ⟨eG⟩⟩
  apply J.superset_covering ?_ (hF y)
  intro W g hg
  rcases hg with ⟨x, ⟨eF⟩⟩
  exact ⟨x, ⟨CartesianBasedFunctor.EssentialImage.compIso
    (F := FiberedCategoryOver.toCartesianBasedFunctor F)
    (G := FiberedCategoryOver.toCartesianBasedFunctor G) f g z y x eF eG⟩⟩

/-- An equivalence over the base is locally essentially surjective on fiber objects. -/
theorem LocallyEssentiallySurjective.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    LocallyEssentiallySurjective J F := by
  rcases hF.nonempty with ⟨e⟩
  intro U y
  apply J.superset_covering ?_ (J.top_mem U)
  intro V f _
  let z := f⁎[Y.chosenCleavage] y
  refine ⟨(e.inverse.fiberFunctor V).obj z, ⟨?_⟩⟩
  exact (((BasedCategory.fiberFunctor Y.toBasedCategory Y.toBasedCategory V).mapIso
    e.counitIso).app z)

/-- Precomposition by an equivalence over the base preserves local essential surjectivity. -/
theorem LocallyEssentiallySurjective.comp_left_of_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} (E : X ⟶ Y)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (G : Y ⟶ Z) (hG : LocallyEssentiallySurjective J G) :
    LocallyEssentiallySurjective J (E ≫ G) := by
  exact LocallyEssentiallySurjective.comp
    (LocallyEssentiallySurjective.of_isEquivalence J E hE) hG

/-- Postcomposition by an equivalence over the base preserves local essential surjectivity. -/
theorem LocallyEssentiallySurjective.comp_right_of_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} (F : X ⟶ Y)
    (hF : LocallyEssentiallySurjective J F) (E : Y ⟶ Z)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence) :
    LocallyEssentiallySurjective J (F ≫ E) := by
  exact hF.comp (LocallyEssentiallySurjective.of_isEquivalence J E hE)

/-- Local essential surjectivity reflects across postcomposition by an equivalence over the
base. -/
theorem LocallyEssentiallySurjective.of_comp_right_isEquivalence
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} (F : X ⟶ Y) (E : Y ⟶ Z)
    (hE : (FiberedCategoryOver.toBasedFunctor E).IsEquivalence)
    (hFE : LocallyEssentiallySurjective J (F ≫ E)) :
    LocallyEssentiallySurjective J F := by
  rcases hE.nonempty with ⟨e⟩
  intro U y
  apply J.superset_covering ?_ (hFE ((FiberedCategoryOver.fiberFunctor E U).obj y))
  intro V f hf
  rcases hf with ⟨x, ⟨c⟩⟩
  let unit := (BasedCategory.fiberFunctor Y.toBasedCategory Y.toBasedCategory V).mapIso
    e.unitIso
  refine ⟨x, ⟨?_⟩⟩
  exact unit.app ((FiberedCategoryOver.fiberFunctor F V).obj x) ≪≫
    (e.inverse.fiberFunctor V).mapIso
      (c ≪≫ FiberedCategoryOver.Reindex.mapIso E f y) ≪≫
        (unit.app (f⁎[Y.chosenCleavage] y)).symm

/-- Transport local essential surjectivity along an isomorphism of parallel
morphisms of fibered categories. -/
theorem LocallyEssentiallySurjective.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : LocallyEssentiallySurjective J F) :
    LocallyEssentiallySurjective J G := by
  intro U y
  apply J.superset_covering ?_ (hF y)
  intro V f hf
  rcases hf with ⟨x, ⟨c⟩⟩
  refine ⟨x, ⟨?_⟩⟩
  exact (((FiberedCategoryOver.fiberHomFunctor X Y V).mapIso e).app x).symm ≪≫ c

/-- Parallel isomorphic morphisms of fibered categories are locally
essentially surjective simultaneously. -/
theorem LocallyEssentiallySurjective.iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    LocallyEssentiallySurjective J F ↔ LocallyEssentiallySurjective J G := by
  exact ⟨LocallyEssentiallySurjective.of_iso e, LocallyEssentiallySurjective.of_iso e.symm⟩

/-- If a composite is locally essentially surjective, then so is its right
factor. -/
theorem LocallyEssentiallySurjective.right_of_comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (h : LocallyEssentiallySurjective J (F ≫ G)) :
    LocallyEssentiallySurjective J G := by
  intro U z
  apply J.superset_covering ?_ (h z)
  intro V f hf
  rcases hf with ⟨x, hx⟩
  exact ⟨(FiberedCategoryOver.fiberFunctor F V).obj x, hx⟩

/-- A right factor is locally essentially surjective when its composite is
isomorphic to a locally essentially surjective morphism. -/
theorem LocallyEssentiallySurjective.right_of_comp_iso
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    {H : X ⟶ Z} (e : F ≫ G ≅ H)
    (hH : LocallyEssentiallySurjective J H) :
    LocallyEssentiallySurjective J G := by
  exact LocallyEssentiallySurjective.right_of_comp
    (LocallyEssentiallySurjective.of_iso e.symm hH)

/-- A morphism of fibred categories locally lifts fiber morphisms when its canonical
Hom-presheaf maps are locally surjective on every slice site. -/
abbrev LocallyLifts
    (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  Homwise.IsLocallySurjective J F

/-- The source-facing local lifting condition is exactly homwise local surjectivity of the
canonical Hom-presheaf maps. -/
theorem LocallyLifts.iff_homwise
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    LocallyLifts J F ↔ Homwise.IsLocallySurjective J F := Iff.rfl

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
              ((FiberedCategoryOver.fiberFunctor F I.Y).map a) := by
  exact CartesianBasedFunctor.LocallyLifts.iff_forall_cover
    (F := FiberedCategoryOver.toCartesianBasedFunctor F)

/-- Local lifting of fiber morphisms is stable under composition. -/
theorem LocallyLifts.comp
    {Z : FiberedCategoryOver.{u, v, w, vS} C}
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : LocallyLifts J F) (hG : LocallyLifts J G) :
    LocallyLifts J (F ≫ G) := by
  exact Homwise.IsLocallySurjective.comp hF hG

/-- An equivalence over the base locally lifts fiber morphisms. -/
theorem LocallyLifts.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    LocallyLifts J F := by
  intro U x y
  letI := CartesianBasedFunctor.HomPresheaf.Chosen.map.isIso_of_isEquivalence
    (FiberedCategoryOver.toCartesianBasedFunctor F) hF x y
  infer_instance

/-- Transport local lifting of fiber morphisms along an isomorphism of parallel morphisms. -/
theorem LocallyLifts.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : LocallyLifts J F) :
    LocallyLifts J G := by
  exact Homwise.IsLocallySurjective.of_iso e hF

/-- Parallel isomorphic morphisms locally lift fiber morphisms simultaneously. -/
theorem LocallyLifts.iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    LocallyLifts J F ↔ LocallyLifts J G := by
  exact ⟨LocallyLifts.of_iso e, LocallyLifts.of_iso e.symm⟩

end FiberedCategoryOver.Hom

end CategoryTheory
