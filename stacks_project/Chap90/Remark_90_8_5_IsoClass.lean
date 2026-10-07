module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal
public import stacks_project.Chap90.Remarks_90_5_2_Grothendieck
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass

/-!
# Canonical morphism to fibrewise isomorphism classes

A category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` has a canonical
based morphism to the category of elements of its fibrewise isomorphism-class functor.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

variable {F : Type w} [Category.{v} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]

/-- The underlying functor of the canonical morphism from a category cofibered in
groupoids to the category of elements of its fibrewise isomorphism-class functor. -/
noncomputable def toIsoClassFunctor :
    F ⥤ (Functor.fiberIsoClassFunctor p).Elements where
  obj x := ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩
  map φ := ⟨p.map φ, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The canonical based morphism from a category cofibered in groupoids to the
category of elements of its fibrewise isomorphism-class functor. -/
noncomputable def toIsoClass :
    BasedCategory.ofFunctor p ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π (Functor.fiberIsoClassFunctor p)) :=
  ofFunctor (toIsoClassFunctor p) sorry

/-- On objects, `toIsoClassFunctor p` sends `x` to the pair consisting of its image
under `p` and the isomorphism class of `x` in the fibre. -/
theorem toIsoClassFunctor_obj (x : F) :
    (toIsoClassFunctor p).obj x =
      ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩ := sorry

/-- On objects, `toIsoClass p` sends `x` to the pair consisting of its image under `p`
and the isomorphism class of `x` in the fibre. -/
theorem toIsoClass_obj (x : F) :
    (toIsoClass p).obj x =
      ⟨p.obj x, Quotient.mk'' (Functor.Fiber.mk (rfl : p.obj x = p.obj x))⟩ := sorry

/-- The image of a morphism under `toIsoClass p` lies over `p.map φ`. -/
theorem toIsoClass_map {x y : F} (φ : x ⟶ y) :
    (CategoryOfElements.π (Functor.fiberIsoClassFunctor p)).map ((toIsoClass p).map φ) =
      p.map φ := sorry

/-- The canonical morphism `toIsoClass p` lies strictly over `ArtinianLocalAlgCat Λ k`. -/
theorem toIsoClass_comp_π :
    (toIsoClass p).toFunctor ⋙ CategoryOfElements.π (Functor.fiberIsoClassFunctor p) = p :=
  sorry

end CategoryTheory.BasedFunctor
