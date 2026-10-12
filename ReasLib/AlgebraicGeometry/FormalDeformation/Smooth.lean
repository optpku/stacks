/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal

/-!
# Smooth morphisms of categories cofibered in groupoids

A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is
smooth when it satisfies the infinitesimal lifting property along surjections.
-/

@[expose] public section

open CategoryTheory

universe u v w v' w'

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- A morphism of categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k` is
smooth if every lifting problem along a surjection `f : B ⟶ A` has a solution. -/
class IsSmooth {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) : Prop where
  /-- Given `α : y ⟶ φ.obj x` over a surjection `f : B ⟶ A`, there exist `x'` over `B`,
  a morphism `x' ⟶ x` over `f`, and a morphism `φ.obj x' ⟶ y` over `𝟙 B` making the
  triangle commute. -/
  exists_lift {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
      {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x) (hα : Y.p.IsHomLift f α) :
      ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
        X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β

/-- The projection of `BasedCategory.ofFunctor p` is cofibered in groupoids as soon
as `p.op` is. -/
instance instIsFiberedInGroupoidsOpOfFunctor {F : Type w} [Category.{v} F]
    {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.IsFibered.InGroupoids p.op] :
    Functor.IsFibered.InGroupoids (BasedCategory.ofFunctor p).p.op :=
  inferInstanceAs (Functor.IsFibered.InGroupoids p.op)

/-- The identity based functor of a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` is smooth. -/
instance instIsSmoothId {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] :
    IsSmooth (id X : X ⥤ᵇ X) := sorry

/-- Smoothness supplies a lift along every surjection, with the over-`f` cell, the
vertical over-`𝟙 B` cell, and triangle commutativity. -/
theorem IsSmooth.spec {X : BasedCategory.{v, w} (ArtinianLocalAlgCat Λ k)}
    {Y : BasedCategory.{v', w'} (ArtinianLocalAlgCat Λ k)}
    [Functor.IsFibered.InGroupoids X.p.op] [Functor.IsFibered.InGroupoids Y.p.op]
    (φ : X ⥤ᵇ Y) [IsSmooth φ] {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) {y : Y.obj} {x : X.obj} (α : y ⟶ φ.obj x)
    (hα : Y.p.IsHomLift f α) :
    ∃ (x' : X.obj) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
      X.p.IsHomLift f β ∧ Y.p.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β := sorry

variable {F : Type w} [Category.{v} F]
variable {G : Type w'} [Category.{v'} G]

/-- A based functor between categories cofibered in groupoids is smooth exactly
when every lifting problem along a surjective base map has a compatible solution. -/
theorem isSmooth_iff {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
    [Functor.IsFibered.InGroupoids p.op] [Functor.IsFibered.InGroupoids q.op]
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) :
    IsSmooth φ ↔
      ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A), Function.Surjective f.hom →
        ∀ {y : G} {x : F} (α : y ⟶ φ.obj x), q.IsHomLift f α →
          ∃ (x' : F) (β : x' ⟶ x) (γ : φ.obj x' ⟶ y),
            p.IsHomLift f β ∧ q.IsHomLift (𝟙 B) γ ∧ γ ≫ α = φ.map β := sorry

end CategoryTheory.BasedFunctor
