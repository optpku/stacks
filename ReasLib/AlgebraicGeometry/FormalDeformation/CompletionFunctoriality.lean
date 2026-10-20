module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Completion
public import ReasLib.CategoryTheory.Cofibered.InGroupoids
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Lift.Construction

/-!
# Functoriality of completion

Based functors and vertical natural transformations act stagewise on formal objects.
These actions define a strict pseudofunctor on categories cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids ObjectProperty
open scoped BasedFunctor Bicategory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace FormalObject

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

section

variable {X Y : BasedCategory.{v, v} (ArtinianLocalAlgCat Λ k)}

/-- Whiskering a formal inverse system by a based functor preserves its stagewise bases. -/
private theorem mapObjOverObj (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    ∀ n : ℕ, Y.p.obj (SequentialInverseSystem.family (ξ.system ⋙ φ.toFunctor) n) =
      ξ.base.truncation n := sorry

/-- Whiskering a formal inverse system preserves the lifts of successor truncation maps. -/
private theorem mapObjOverStep (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    ∀ n : ℕ, Y.p.IsHomLift (ξ.base.truncationMap n)
      (SequentialInverseSystem.stepMap (ξ.system ⋙ φ.toFunctor) n) := sorry

/-- The formal object obtained by whiskering its inverse system by a based functor. -/
private def mapObj (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) : FormalObject Y.p :=
  ⟨ξ.base, ξ.system ⋙ φ.toFunctor, mapObjOverObj φ ξ, mapObjOverStep φ ξ⟩

/-- A based functor preserves the truncated-base lift conditions of a formal morphism. -/
private theorem mapHomOver (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) :
    ∀ n : ℕ, Y.p.IsHomLift (a.baseTrunc n) (φ.map (a.app n)) := sorry

/-- Applying a based functor to stage maps preserves their successor naturality. -/
private theorem mapHomNaturality (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) :
    ∀ n : ℕ, (mapObj φ ξ).system.stepMap n ≫ φ.map (a.app n) =
      φ.map (a.app (n + 1)) ≫ (mapObj φ η).system.stepMap n := sorry

/-- The formal morphism with unchanged base maps and functorially mapped stage maps. -/
private def mapHom (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) :
    mapObj φ ξ ⟶ mapObj φ η :=
  Hom.of a.base (fun n ↦ φ.map (a.app n)) a.baseTrunc
    (mapHomOver φ a) a.baseTrunc_spec (mapHomNaturality φ a)

/-- The stagewise action on formal morphisms preserves identities. -/
private theorem mapId (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    mapHom φ (𝟙 ξ) = 𝟙 (mapObj φ ξ) := sorry

/-- The stagewise action on formal morphisms preserves composition. -/
private theorem mapComp (φ : X ⥤ᵇ Y) {ξ η ζ : FormalObject X.p}
    (a : ξ ⟶ η) (b : η ⟶ ζ) :
    mapHom φ (a ≫ b) = mapHom φ a ≫ mapHom φ b := sorry

/-- The functor on formal objects induced by a based functor keeps the complete local
base and whiskers the inverse system with its underlying functor. -/
def map (φ : X ⥤ᵇ Y) : FormalObject X.p ⥤ FormalObject Y.p where
  obj := mapObj φ
  map := mapHom φ
  map_id := mapId φ
  map_comp := mapComp φ

/-- Mapping a formal object along a based functor preserves the complete local base. -/
theorem map_base (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    ((map φ).obj ξ).base = ξ.base := sorry

/-- Mapping a formal object whiskers its inverse system with the underlying functor. -/
theorem map_system (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    ((map φ).obj ξ).system = ξ.system ⋙ φ.toFunctor := sorry

/-- Every stage of a mapped formal object is the image of the original stage. -/
theorem map_family (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) (n : ℕ) :
    ((map φ).obj ξ).system.family n = φ.obj (ξ.system.family n) := sorry

/-- Successor transitions of a mapped formal object are images of the original transitions. -/
theorem map_step (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) (n : ℕ) :
    ((map φ).obj ξ).system.stepMap n = φ.map (ξ.system.stepMap n) := sorry

/-- Mapping a formal morphism preserves its complete local base map. -/
theorem map_map_base (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) :
    ((map φ).map a).base = a.base := sorry

/-- Mapping a formal morphism applies the based functor to each stage map. -/
theorem map_map_app (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) (n : ℕ) :
    ((map φ).map a).app n = φ.map (a.app n) := sorry

/-- The stage components of a vertical natural transformation lift identity truncation maps. -/
private theorem map₂AppOver {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) :
    ∀ n : ℕ, Y.p.IsHomLift (𝟙 (ξ.base.truncation n))
      (t.toNatTrans.app (ξ.system.family n)) := sorry

/-- Identity truncated-base maps are compatible with the identity complete-base map. -/
private theorem map₂AppBaseTruncSpec {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ)
    (ξ : FormalObject X.p) :
    ∀ n : ℕ,
      (ArtinianLocalAlgCat.Hom.toRingHom (𝟙 (ξ.base.truncation n))).comp
          (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))) =
        (Ideal.Quotient.mk (CompleteLocalAlgCat.maximalIdeal ξ.base ^ (n + 1))).comp
          (CompleteLocalAlgCat.Hom.toRingHom (𝟙 ξ.base)) := sorry

/-- The stage components of a vertical natural transformation commute with successor maps. -/
private theorem map₂AppNaturality {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) :
    ∀ n : ℕ, ((map φ).obj ξ).system.stepMap n ≫ t.toNatTrans.app (ξ.system.family n) =
      t.toNatTrans.app (ξ.system.family (n + 1)) ≫ ((map ψ).obj ξ).system.stepMap n := sorry

/-- The formal morphism induced by a vertical natural transformation at a formal object. -/
private def map₂App {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) :
    (map φ).obj ξ ⟶ (map ψ).obj ξ :=
  Hom.of (𝟙 ξ.base) (fun n ↦ t.toNatTrans.app (ξ.system.family n))
    (fun n ↦ 𝟙 (ξ.base.truncation n))
    (map₂AppOver t ξ) (map₂AppBaseTruncSpec t ξ) (map₂AppNaturality t ξ)

/-- The induced formal morphisms are natural in formal objects. -/
private theorem map₂Naturality {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ)
    {ξ η : FormalObject X.p} (a : ξ ⟶ η) :
    (map φ).map a ≫ map₂App t η = map₂App t ξ ≫ (map ψ).map a := sorry

/-- The natural transformation induced on formal objects has identity base maps and
components given by the original transformation at each stage object. -/
def map₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : map φ ⟶ map ψ where
  app := map₂App t
  naturality := fun {_ _} a ↦ map₂Naturality t a

/-- The base map of the induced natural transformation at a formal object is the identity. -/
theorem map₂_app_base {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) :
    ((map₂ t).app ξ).base = 𝟙 ξ.base := sorry

/-- Each stage component of the induced transformation is the original component at that stage. -/
theorem map₂_app_app {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) (n : ℕ) :
    ((map₂ t).app ξ).app n = t.toNatTrans.app (ξ.system.family n) := sorry

variable [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]

/-- The functor induced on formal objects commutes with projection to complete local bases. -/
theorem basedMap_w (φ : X ⥤ᵇ Y) :
    map φ ⋙ Functor.completion Y.p = Functor.completion X.p := sorry

/-- The based functor of completions induced by a based functor over the Artinian local base. -/
def basedMap (φ : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (Functor.completion X.p) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion Y.p) where
  toFunctor := map φ
  w := basedMap_w φ

/-- Each component of the induced transformation lies over the identity complete-base map. -/
private theorem basedMap₂IsHomLift {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) :
    ∀ ξ : FormalObject X.p,
      (Functor.completion Y.p).IsHomLift
        (𝟙 ((Functor.completion X.p).obj ξ)) ((map₂ t).app ξ) := sorry

/-- The based natural transformation of completions induced by a vertical transformation. -/
def basedMap₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : basedMap φ ⟶ basedMap ψ where
  toNatTrans := map₂ t
  isHomLift' := basedMap₂IsHomLift t

end

/-- Completion of the identity based functor is the identity of the completion. -/
private theorem completionMapId
    (X : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)) :
    basedMap (toBasedFunctor (𝟙 X)) = 𝟙 (BasedCategory.ofFunctor (Functor.completion X.p)) := sorry

/-- Completion preserves composition of based functors. -/
private theorem completionMapComp
    {X Y Z : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    basedMap (toBasedFunctor (φ ≫ ψ)) =
      basedMap (toBasedFunctor φ) ⋙ basedMap (toBasedFunctor ψ) := sorry

/-- Completion preserves identity vertical transformations. -/
private theorem completionMap₂Id
    {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) :
    basedMap₂ (toBasedNatTrans (𝟙 φ)) = 𝟙 (basedMap (toBasedFunctor φ)) := sorry

/-- Completion preserves vertical composition of transformations. -/
private theorem completionMap₂Comp
    {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    {φ ψ χ : X ⟶ Y} (t : φ ⟶ ψ) (s : ψ ⟶ χ) :
    basedMap₂ (toBasedNatTrans (t ≫ s)) =
      basedMap₂ (toBasedNatTrans t) ≫ basedMap₂ (toBasedNatTrans s) := sorry

/-- Completion preserves left whiskering, with transport along its composition equation. -/
private theorem completionMap₂WhiskerLeft
    {X Y Z : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) {ψ ψ' : Y ⟶ Z} (t : ψ ⟶ ψ') :
    basedMap₂ (toBasedNatTrans (φ ◁ t)) = eqToHom (completionMapComp φ ψ) ≫
      BasedCategory.whiskerLeft (basedMap (toBasedFunctor φ))
        (basedMap₂ (toBasedNatTrans t)) ≫
        eqToHom (completionMapComp φ ψ').symm := sorry

/-- Completion preserves right whiskering, with transport along its composition equation. -/
private theorem completionMap₂WhiskerRight
    {X Y Z : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    {φ φ' : X ⟶ Y} (t : φ ⟶ φ') (ψ : Y ⟶ Z) :
    basedMap₂ (toBasedNatTrans (t ▷ ψ)) = eqToHom (completionMapComp φ ψ) ≫
      BasedCategory.whiskerRight (basedMap₂ (toBasedNatTrans t))
        (basedMap (toBasedFunctor ψ)) ≫
        eqToHom (completionMapComp φ' ψ).symm := sorry

/-- The strict pseudofunctor sending a category cofibered in groupoids over the Artinian
local base to its completion as a based category over the complete local base. -/
def completionAmbient :
    StrictPseudofunctor
      (CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
      (BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :=
  StrictPseudofunctor.mk''
    { obj := fun X ↦ BasedCategory.ofFunctor (Functor.completion X.p)
      map := fun φ ↦ basedMap (toBasedFunctor φ)
      map₂ := fun t ↦ basedMap₂ (toBasedNatTrans t)
      map_id := completionMapId
      map_comp := completionMapComp
      map₂_id := completionMap₂Id
      map₂_comp := completionMap₂Comp
      map₂_whisker_left := completionMap₂WhiskerLeft
      map₂_whisker_right := completionMap₂WhiskerRight }

/-- Ambient completion sends a cofibered category to the based category of its formal objects. -/
theorem completionAmbient_obj
    (X : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)) :
    completionAmbient.obj X = BasedCategory.ofFunctor (Functor.completion X.p) := sorry

end FormalObject

namespace CategoryTheory.Functor

/-- Completion acts stagewise on functors and vertical natural transformations and
defines a strict pseudofunctor between categories cofibered in groupoids over the
Artinian local and complete local bases. -/
noncomputable def completionStrictPseudofunctor :
    StrictPseudofunctor
      (CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
      (CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) v, max u v}
        (CompleteLocalAlgCat Λ k)) :=
  FullSubbicategory.lift FormalObject.completionAmbient
    (fun X ↦ completion_op_isFiberedInGroupoids X.p)

/-- The completion pseudofunctor sends a cofibered category to the completion of its projection. -/
theorem completionStrictPseudofunctor_obj
    (X : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)) :
    (completionStrictPseudofunctor.obj X).p = completion X.p := sorry

/-- The completion pseudofunctor sends a morphism to its induced based functor of formal objects. -/
theorem completionStrictPseudofunctor_map
    {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    (φ : X ⟶ Y) :
    toBasedFunctor (completionStrictPseudofunctor.map φ) =
      FormalObject.basedMap (toBasedFunctor φ) := sorry

/-- The completion pseudofunctor sends a vertical transformation to its induced based transformation. -/
theorem completionStrictPseudofunctor_map₂
    {X Y : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)}
    {φ φ' : X ⟶ Y} (t : φ ⟶ φ') :
    toBasedNatTrans (completionStrictPseudofunctor.map₂ t) =
      FormalObject.basedMap₂ (toBasedNatTrans t) := sorry

end CategoryTheory.Functor

end
