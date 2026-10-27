/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Local
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Gerbe morphisms of fibred categories

The universe-polymorphic owner is `CartesianBasedFunctor.IsGerbeMorphism`. This file exposes its
fixed-universe view for the bicategorical hom-category of fibred categories, together with
readouts in the established unlifted Hom-presheaf language.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Hom

variable {X Y Z : FiberedCategoryOver.{u, v, w, vS} C}

/-- A morphism of fibred categories is a gerbe morphism when it is locally essentially
surjective on objects and locally surjective on every canonical Hom-presheaf. This is the
fixed-universe specialization of `CartesianBasedFunctor.IsGerbeMorphism`. -/
@[stacks 06P2 "gerbe morphism of fibred categories"]
abbrev IsGerbeMorphism (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  CartesianBasedFunctor.IsGerbeMorphism J
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- The two defining local conditions of a gerbe morphism. -/
@[stacks 06P2 "fixed-universe gerbe-morphism criterion"]
theorem isGerbeMorphism_iff
    (J : GrothendieckTopology C) (F : X ⟶ Y) :
    IsGerbeMorphism J F ↔
      LocallyEssentiallySurjective J F ∧
        Homwise.IsLocallySurjective J F := Iff.rfl

/-- A gerbe morphism is locally essentially surjective on fibre objects. -/
@[stacks 06P2 "fixed-universe objectwise readout"]
theorem IsGerbeMorphism.locallyEssentiallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    LocallyEssentiallySurjective J F := hF.1

/-- A gerbe morphism locally lifts fibre morphisms. -/
@[stacks 06P2 "fixed-universe local-lifting readout"]
theorem IsGerbeMorphism.locallyLifts
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    LocallyLifts J F := hF.2

/-- A gerbe morphism is locally surjective on every canonical Hom-presheaf. -/
@[stacks 06P2 "fixed-universe Hom-presheaf readout"]
theorem IsGerbeMorphism.homwiseLocallySurjective
    {J : GrothendieckTopology C} {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    Homwise.IsLocallySurjective J F := hF.2

private theorem homwiseLocallySurjective_of_fiberwiseFull
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : ∀ U : C, ((FiberedCategoryOver.toCartesianBasedFunctor F).fiberFunctor U).Full) :
    Homwise.IsLocallySurjective J F := by
  intro U x y
  apply Presheaf.isLocallySurjective_of_surjective
  intro W b
  let ex := CartesianBasedFunctor.Reindex.mapIso
    (FiberedCategoryOver.toCartesianBasedFunctor F)
    (Functor.Cleavage.ofIsFibered X.p) (Functor.Cleavage.ofIsFibered Y.p)
    W.unop.hom x
  let ey := CartesianBasedFunctor.Reindex.mapIso
    (FiberedCategoryOver.toCartesianBasedFunctor F)
    (Functor.Cleavage.ofIsFibered X.p) (Functor.Cleavage.ofIsFibered Y.p)
    W.unop.hom y
  letI := hF W.unop.left
  obtain ⟨a, ha⟩ := ((FiberedCategoryOver.toCartesianBasedFunctor F).fiberFunctor
    W.unop.left).map_surjective (ex.inv ≫ b.down ≫ ey.hom)
  refine ⟨ULift.up a, ?_⟩
  apply ULift.ext
  change ex.hom ≫ ((FiberedCategoryOver.toCartesianBasedFunctor F).fiberFunctor
    W.unop.left).map a ≫ ey.inv = b.down
  rw [ha]
  simp only [Category.assoc, ex.hom_inv_id_assoc]
  exact (congrArg (fun k ↦ b.down ≫ k) ey.hom_inv_id).trans (Category.comp_id _)

/-- The identity morphism is a gerbe morphism. -/
@[stacks 06R3 "identity gerbe morphism"]
theorem IsGerbeMorphism.id (J : GrothendieckTopology C) :
    IsGerbeMorphism J (𝟙 X) := by
  refine ⟨?_, homwiseLocallySurjective_of_fiberwiseFull J (𝟙 X) (fun U ↦ ?_)⟩
  · intro U y
    apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
    intro V f _
    exact ⟨f⁎[X.chosenCleavage] y, ⟨Iso.refl _⟩⟩
  · change (𝟭 (X.p.Fiber U)).Full
    infer_instance

/-- Gerbe morphisms of fibred categories are closed under composition. -/
@[stacks 06R3]
theorem IsGerbeMorphism.comp
    {J : GrothendieckTopology C} {F : X ⟶ Y} {G : Y ⟶ Z}
    (hF : IsGerbeMorphism J F) (hG : IsGerbeMorphism J G) :
    IsGerbeMorphism J (F ≫ G) := sorry

/-- The gerbe-morphism property of fibred categories is preserved when the topology is
enlarged. -/
theorem IsGerbeMorphism.of_le
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    {F : X ⟶ Y} (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism K F := by
  refine ⟨fun {U} y ↦ hJK U (hF.1 y), ?_⟩
  intro U x y
  exact Presheaf.isLocallySurjective_of_le (fun V _ hV ↦ hJK V.left hV)
    _ (hF.2 x y)

/-- An equivalence over the base is a gerbe morphism. -/
theorem IsGerbeMorphism.of_isEquivalence
    (J : GrothendieckTopology C) (F : X ⟶ Y)
    (hF : (FiberedCategoryOver.toBasedFunctor F).IsEquivalence) :
    IsGerbeMorphism J F := by
  rcases hF.nonempty with ⟨e⟩
  constructor
  · intro U y
    apply J.superset_covering (S := ⊤) ?_ (J.top_mem U)
    intro V f _
    let z := f⁎[Y.chosenCleavage] y
    refine ⟨(e.inverse.fiberFunctor V).obj z, ⟨?_⟩⟩
    exact (((BasedCategory.fiberFunctor Y.toBasedCategory Y.toBasedCategory V).mapIso
      e.counitIso).app z)
  · apply homwiseLocallySurjective_of_fiberwiseFull J F
    intro U
    letI : ((FiberedCategoryOver.toCartesianBasedFunctor F).fiberFunctor U).IsEquivalence :=
      Functor.IsEquivalence.mk' (e.inverse.fiberFunctor U)
        ((BasedCategory.fiberFunctor X.toBasedCategory X.toBasedCategory U).mapIso e.unitIso)
        ((BasedCategory.fiberFunctor Y.toBasedCategory Y.toBasedCategory U).mapIso e.counitIso)
    infer_instance

/-- Transport the gerbe-morphism property along an isomorphism of parallel morphisms. -/
theorem IsGerbeMorphism.of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G)
    (hF : IsGerbeMorphism J F) :
    IsGerbeMorphism J G := sorry

/-- Isomorphic parallel morphisms are gerbe morphisms simultaneously. -/
theorem isGerbeMorphism_iff_of_iso
    {J : GrothendieckTopology C} {F G : X ⟶ Y} (e : F ≅ G) :
    IsGerbeMorphism J F ↔ IsGerbeMorphism J G := by
  exact ⟨IsGerbeMorphism.of_iso e, IsGerbeMorphism.of_iso e.symm⟩

end FiberedCategoryOver.Hom

end CategoryTheory
