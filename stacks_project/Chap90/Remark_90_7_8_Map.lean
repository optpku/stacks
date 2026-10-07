module

public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Remark_90_7_8_Groupoids

/-!
# Stagewise action of a based functor on formal objects

A based functor over `ArtinianLocalAlgCat Λ k` acts on formal objects by whiskering
the inverse system and applying the functor to stage maps, inducing a based functor
of completions over `CompleteLocalAlgCat Λ k`. Vertical `2`-cells act by their
components at the stage objects.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped BasedFunctor Bicategory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

noncomputable section

namespace FormalObject

section

variable {X Y : BasedCategory.{v, v} (ArtinianLocalAlgCat Λ k)}

/-- The functor on formal objects induced by a based functor `φ` over `C_Λ`. It keeps
the complete local base and whiskers the inverse system with `φ.toFunctor`. -/
def map (φ : X ⥤ᵇ Y) : FormalObject X.p ⥤ FormalObject Y.p where
  obj ξ :=
    { base := ξ.base
      system := ξ.system ⋙ φ.toFunctor
      over_obj := sorry
      over_step := sorry }
  map a :=
    { base := a.base
      app := fun n ↦ φ.map (a.app n)
      baseTrunc := a.baseTrunc
      over := sorry
      baseTrunc_spec := sorry
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Mapping a formal object along `φ` preserves the complete local base. -/
theorem map_base (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    ((map φ).obj ξ).base = ξ.base := sorry

/-- Mapping a formal object along `φ` whiskers its inverse system with `φ.toFunctor`. -/
theorem map_system (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) :
    ((map φ).obj ξ).system = ξ.system ⋙ φ.toFunctor := sorry

/-- Stage `n` of a mapped formal object is the image of the original stage under `φ`. -/
theorem map_family (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) (n : ℕ) :
    ((map φ).obj ξ).system.family n = φ.obj (ξ.system.family n) := sorry

/-- Successor transitions of a mapped formal object are the images of the original
transitions under `φ`. -/
theorem map_step (φ : X ⥤ᵇ Y) (ξ : FormalObject X.p) (n : ℕ) :
    ((map φ).obj ξ).system.stepMap n = φ.map (ξ.system.stepMap n) := sorry

/-- Mapping a morphism of formal objects preserves the complete local base map. -/
theorem map_map_base (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) :
    ((map φ).map a).base = a.base := sorry

/-- Mapping a morphism of formal objects applies `φ` to each stage map. -/
theorem map_map_app (φ : X ⥤ᵇ Y) {ξ η : FormalObject X.p} (a : ξ ⟶ η) (n : ℕ) :
    ((map φ).map a).app n = φ.map (a.app n) := sorry

/-- The natural transformation of formal-object functors induced by a based
`2`-morphism `t`. Components keep the identity base map and apply `t` at each
stage object. -/
def map₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : map φ ⟶ map ψ where
  app ξ :=
    { base := 𝟙 ξ.base
      app := fun n ↦ t.toNatTrans.app (ξ.system.family n)
      baseTrunc := fun n ↦ 𝟙 (ξ.base.truncation n)
      over := sorry
      baseTrunc_spec := sorry
      naturality := sorry }
  naturality := sorry

/-- The base map of a mapped `2`-cell at a formal object is the identity. -/
theorem map₂_app_base {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) :
    ((map₂ t).app ξ).base = 𝟙 ξ.base := sorry

/-- The stage-`n` component of a mapped `2`-cell is the component of `t` at that stage. -/
theorem map₂_app_app {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) (ξ : FormalObject X.p) (n : ℕ) :
    ((map₂ t).app ξ).app n = t.toNatTrans.app (ξ.system.family n) := sorry

variable [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]

/-- The based functor of completions over `Ĉ_Λ` induced by a based functor over `C_Λ`. -/
def basedMap (φ : X ⥤ᵇ Y) :
    BasedCategory.ofFunctor (Functor.completion X.p) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion Y.p) where
  toFunctor := map φ
  w := sorry

/-- The induced based functor of completions lies over the identity of `Ĉ_Λ`: it preserves
complete local bases. -/
theorem basedMap_w (φ : X ⥤ᵇ Y) :
    (basedMap φ).toFunctor ⋙ Functor.completion Y.p = Functor.completion X.p := sorry

/-- The based `2`-morphism of completions induced by a based `2`-morphism over `C_Λ`. -/
def basedMap₂ {φ ψ : X ⥤ᵇ Y} (t : φ ⟶ ψ) : basedMap φ ⟶ basedMap ψ where
  toNatTrans := map₂ t
  isHomLift' := sorry

end

/-- The ambient strict `2`-functor sending a category cofibered in groupoids over `C_Λ`
to its completion, as a based category over `Ĉ_Λ`. -/
def completionAmbient :
    StrictPseudofunctor
      (CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k))
      (BasedCategory.{max u v, max (u + 1) v} (CompleteLocalAlgCat Λ k)) :=
  StrictPseudofunctor.mk''
    { obj := fun X ↦ BasedCategory.ofFunctor (Functor.completion X.p)
      map := fun φ ↦ basedMap (toBasedFunctor φ)
      map₂ := fun t ↦ basedMap₂ (toBasedNatTrans t)
      map_id := sorry
      map_comp := sorry
      map₂_id := sorry
      map₂_comp := sorry
      map₂_whisker_left := sorry
      map₂_whisker_right := sorry }

/-- The ambient completion `2`-functor sends a cofibered category to the based category
of its formal objects. -/
theorem completionAmbient_obj
    (X : CofiberedCategoryOver.Groupoids.{u + 1, u, v, v} (ArtinianLocalAlgCat Λ k)) :
    completionAmbient.obj X = BasedCategory.ofFunctor (Functor.completion X.p) := sorry

end FormalObject

end
