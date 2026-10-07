module

public import ReasLib.CategoryTheory.Homology.HomologicalDeltaFunctor

/-!
# Degreewise isomorphisms of homological delta functors

An isomorphism of homological delta functors evaluates to an isomorphism of ordinary functors in
every degree.  This file is the lower-indexed counterpart of the corresponding cohomological API.
-/

@[expose] public section

noncomputable section

universe vA vB uA uB

namespace CategoryTheory.HomologicalDeltaFunctor.Iso

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {F G : HomologicalDeltaFunctor A B}

/-- The degree-`n` forward and inverse components compose to the identity on the source functor. -/
theorem app_hom_inv_id (e : F ≅ G) (n : ℕ) :
    e.hom.app n ≫ e.inv.app n = 𝟙 (F n).obj := sorry

/-- The degree-`n` inverse and forward components compose to the identity on the target functor. -/
theorem app_inv_hom_id (e : F ≅ G) (n : ℕ) :
    e.inv.app n ≫ e.hom.app n = 𝟙 (G n).obj := sorry

/-- Evaluation of an isomorphism of homological delta functors in degree `n`. -/
@[stacks 010U "degreewise comparison of homological delta functors"]
noncomputable def app (e : F ≅ G) (n : ℕ) : (F n).obj ≅ (G n).obj where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := app_hom_inv_id e n
  inv_hom_id := app_inv_hom_id e n

/-- The forward map of the degreewise isomorphism is the corresponding delta-functor component. -/
@[simp]
theorem app_hom (e : F ≅ G) (n : ℕ) :
    (app e n).hom = e.hom.app n := sorry

/-- The inverse map of the degreewise isomorphism is the corresponding delta-functor component. -/
@[simp]
theorem app_inv (e : F ≅ G) (n : ℕ) :
    (app e n).inv = e.inv.app n := sorry

end CategoryTheory.HomologicalDeltaFunctor.Iso
