/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Injective.Baer.Step

@[expose] public section

/-!
# Functoriality of the One-Step Baer Construction

Reindexing the two categorical coproducts along a module morphism gives a map of the defining
spans and hence a map of pushouts.  This file packages those maps into the Baer step functor and
records its natural monomorphism and ideal-extension API.
-/

open CategoryTheory Limits

universe v u

namespace ModuleCat.Baer

variable (R : Type u) [Ring R]

namespace Index

/-- Postcomposition by `f` sends a Baer index over `M` to one over `N`. -/
abbrev map {M N : ModuleCat.{max u v} R} (f : M ⟶ N) : Index R M → Index R N :=
  fun j ↦ ⟨j.1, j.2 ≫ f⟩

/-- Reindexing by an identity morphism fixes every Baer index. -/
theorem map_id (M : ModuleCat.{max u v} R) (j : Index R M) :
    map R (𝟙 M) j = j := sorry

/-- Reindexing along a composite is iterated reindexing. -/
theorem map_comp {M N P : ModuleCat.{max u v} R} (f : M ⟶ N) (g : N ⟶ P)
    (j : Index R M) :
    map R (f ≫ g) j = map R g (map R f j) := sorry

end Index

/-- The reindexing map between the coproducts of ideal domains. -/
noncomputable def idealCoproductMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    idealCoproduct R M ⟶ idealCoproduct R N :=
  Sigma.map' (Index.map R f) fun _ ↦ 𝟙 _

/-- The reindexing map between the coproducts of copies of `R`. -/
noncomputable def ringCoproductMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    ringCoproduct R M ⟶ ringCoproduct R N :=
  Sigma.map' (Index.map R f) fun _ ↦ 𝟙 _

/-- Reindexing the ideal coproduct sends each coprojection to its reindexed coprojection. -/
@[reassoc (attr := simp)]
theorem idealι_coproductMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N)
    (j : Index R M) :
    idealι R M j ≫ idealCoproductMap R f = idealι R N (Index.map R f j) := sorry

/-- Reindexing the ring coproduct sends each coprojection to its reindexed coprojection. -/
@[reassoc (attr := simp)]
theorem ringι_coproductMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N)
    (j : Index R M) :
    ringι R M j ≫ ringCoproductMap R f = ringι R N (Index.map R f j) := sorry

/-- Reindexing the ideal coproduct preserves identity morphisms. -/
theorem idealCoproductMap_id (M : ModuleCat.{max u v} R) :
    idealCoproductMap R (𝟙 M) = 𝟙 (idealCoproduct R M) := sorry

/-- Reindexing the ideal coproduct preserves composition. -/
theorem idealCoproductMap_comp {M N P : ModuleCat.{max u v} R} (f : M ⟶ N)
    (g : N ⟶ P) :
    idealCoproductMap R (f ≫ g) = idealCoproductMap R f ≫ idealCoproductMap R g := sorry

/-- Reindexing the ring coproduct preserves identity morphisms. -/
theorem ringCoproductMap_id (M : ModuleCat.{max u v} R) :
    ringCoproductMap R (𝟙 M) = 𝟙 (ringCoproduct R M) := sorry

/-- Reindexing the ring coproduct preserves composition. -/
theorem ringCoproductMap_comp {M N P : ModuleCat.{max u v} R} (f : M ⟶ N)
    (g : N ⟶ P) :
    ringCoproductMap R (f ≫ g) = ringCoproductMap R f ≫ ringCoproductMap R g := sorry

/-- The ideal-inclusion side of the Baer span is natural in the module. -/
theorem toRing_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    CommSq (toRing R M) (idealCoproductMap R f)
      (ringCoproductMap R f) (toRing R N) := sorry

/-- The side of the Baer span assembled from ideal maps is natural in the module. -/
theorem toModule_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    CommSq (toModule R M) (idealCoproductMap R f) f (toModule R N) := sorry

/-- The morphism of Baer spans induced by a module morphism. -/
@[stacks 05NW "Baer span morphism"]
noncomputable def spanMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    span (toRing R M) (toModule R M) ⟶ span (toRing R N) (toModule R N) :=
  spanHomMk (idealCoproductMap R f) (ringCoproductMap R f) f
    (toRing_naturality R f).w (toModule_naturality R f).w

/-- The induced morphism of Baer spans preserves identity morphisms. -/
theorem spanMap_id (M : ModuleCat.{max u v} R) :
    spanMap R (𝟙 M) = 𝟙 (span (toRing R M) (toModule R M)) := sorry

/-- The induced morphism of Baer spans preserves composition. -/
theorem spanMap_comp {M N P : ModuleCat.{max u v} R} (f : M ⟶ N) (g : N ⟶ P) :
    spanMap R (f ≫ g) = spanMap R f ≫ spanMap R g := sorry

/-- The defining Baer span, functorial in the target module. -/
@[stacks 05NW "Baer span functor"]
noncomputable def spanFunctor :
    ModuleCat.{max u v} R ⥤ WalkingSpan ⥤ ModuleCat.{max u v} R where
  obj M := span (toRing R M) (toModule R M)
  map := spanMap R
  map_id := spanMap_id R
  map_comp := spanMap_comp R

/-- The one-step Baer construction is the colimit of the functorial Baer span. -/
@[stacks 05NW "Baer step functor"]
noncomputable def stepFunctor : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  spanFunctor R ⋙ colim

/-- The morphism between Baer steps induced by a module morphism. -/
noncomputable abbrev stepMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    step R M ⟶ step R N :=
  (stepFunctor R).map f

/-- The induced map between Baer steps is compatible with the ring-coproduct maps. -/
@[reassoc (attr := simp)]
theorem fromRing_stepMap {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    fromRing R M ≫ stepMap R f = ringCoproductMap R f ≫ fromRing R N := sorry

/-- The canonical inclusions are compatible with the induced maps between Baer steps. -/
@[reassoc (attr := simp)]
theorem inclusion_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    f ≫ inclusion R N = inclusion R M ≫ stepMap R f := sorry

/-- Functor-level naturality of the canonical inclusions into a Baer step. -/
theorem inclusion_naturality_functor ⦃M N : ModuleCat.{max u v} R⦄ (f : M ⟶ N) :
    (𝟭 (ModuleCat.{max u v} R)).map f ≫ inclusion R N =
      inclusion R M ≫ (stepFunctor R).map f := sorry

/-- The canonical Baer inclusions form a natural transformation. -/
@[stacks 05NW "natural Baer inclusion"]
noncomputable def inclusionNatTrans : 𝟭 (ModuleCat.{max u v} R) ⟶ stepFunctor R where
  app := inclusion R
  naturality := inclusion_naturality_functor R

/-- The coproduct of ideal inclusions is a monomorphism. -/
theorem mono_toRing (M : ModuleCat.{max u v} R) : Mono (toRing R M) := sorry

attribute [instance] mono_toRing

/-- The canonical map into a Baer step is a monomorphism. -/
@[stacks 05NW "monomorphic Baer inclusion"]
theorem mono_inclusion (M : ModuleCat.{max u v} R) : Mono (inclusion R M) := sorry

attribute [instance] mono_inclusion

/-- The natural Baer inclusion is a monomorphism in the endofunctor category. -/
@[stacks 05NW "monomorphic Baer inclusion", instance]
theorem mono_inclusionNatTrans : Mono (inclusionNatTrans R) := sorry

/-- Elementwise form of the monomorphism property of the canonical Baer inclusion. -/
theorem inclusion_injective (M : ModuleCat.{max u v} R) :
    Function.Injective (inclusion R M).hom := sorry

/-- The extension from `R` associated to an indexed map from an ideal into `M`. -/
@[stacks 05NW "ideal-map extension"]
noncomputable def liftedIdealLift (M : ModuleCat.{max u v} R) (I : Ideal R)
    (φ : idealObject R I ⟶ M) : ringObject R ⟶ step R M :=
  ringι R M ⟨I, φ⟩ ≫ fromRing R M

/-- `liftedIdealLift` extends the given lifted ideal map across the lifted ideal inclusion. -/
@[stacks 05NW "ideal extension square"]
theorem liftedIdealLift_commSq (M : ModuleCat.{max u v} R) (I : Ideal R)
    (φ : idealObject R I ⟶ M) :
    CommSq ((ModuleCat.uliftFunctor.{v, u, u} R).map (ModuleCat.ofHom I.subtype)) φ
      (liftedIdealLift R M I φ) (inclusion R M) := sorry

/-- Lifted ideal extensions are compatible with morphisms between the target modules. -/
@[reassoc (attr := simp)]
theorem liftedIdealLift_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N)
    (I : Ideal R) (φ : idealObject R I ⟶ M) :
    liftedIdealLift R M I φ ≫ stepMap R f =
      liftedIdealLift R N I (φ ≫ f) := sorry

/-- The lifted ideal object is canonically isomorphic to the original ideal module when no
universe enlargement is needed. -/
def idealObjectIso (I : Ideal R) :
    idealObject.{0, u} R I ≅ ModuleCat.of R I :=
  ULift.moduleEquiv.toModuleIso

/-- The lifted regular module is canonically isomorphic to the original regular module when no
universe enlargement is needed. -/
def ringObjectIso : ringObject.{0, u} R ≅ ModuleCat.of R R :=
  ULift.moduleEquiv.toModuleIso

/-- The extension from `R` associated to an ordinary map from an ideal into a same-universe
module. -/
@[stacks 05NW "ordinary ideal lift"]
noncomputable def idealLift (M : ModuleCat.{u} R) (I : Ideal R)
    (φ : ModuleCat.of R I ⟶ M) : ModuleCat.of R R ⟶ step.{0, u} R M :=
  (ringObjectIso R).inv ≫
    liftedIdealLift.{0, u} R M I ((idealObjectIso R I).hom ≫ φ)

/-- `idealLift` extends an ordinary ideal map across the ideal inclusion. -/
@[stacks 05NW "ordinary ideal extension square"]
theorem idealLift_commSq (M : ModuleCat.{u} R) (I : Ideal R)
    (φ : ModuleCat.of R I ⟶ M) :
    CommSq (ModuleCat.ofHom I.subtype) φ
      (idealLift R M I φ) (inclusion.{0, u} R M) := sorry

/-- Ordinary ideal extensions are natural in the target module. -/
@[reassoc (attr := simp)]
theorem idealLift_naturality {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (I : Ideal R) (φ : ModuleCat.of R I ⟶ M) :
    idealLift R M I φ ≫ stepMap.{0, u} R f = idealLift R N I (φ ≫ f) := sorry

end ModuleCat.Baer
