/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor

/-!
# Degreewise isomorphisms of cohomological delta functors

An isomorphism of cohomological delta functors evaluates to an isomorphism of ordinary functors
in every degree. This file owns that projection, so geometric clients do not rebuild its inverse
laws from the category structure.
-/

@[expose] public section

noncomputable section

universe vA vB uA uB

namespace CategoryTheory.CohomologicalDeltaFunctor.Iso

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {F G : CohomologicalDeltaFunctor A B}

/-- The degree-`n` forward and inverse components of a delta-functor isomorphism compose to the
identity on the source functor. -/
theorem app_hom_inv_id (e : HomIso F G) (n : ℕ) :
    e.hom.app n ≫ e.inv.app n = 𝟙 (F.F n).obj := sorry

/-- The degree-`n` inverse and forward components of a delta-functor isomorphism compose to the
identity on the target functor. -/
theorem app_inv_hom_id (e : HomIso F G) (n : ℕ) :
    e.inv.app n ≫ e.hom.app n = 𝟙 (G.F n).obj := sorry

/-- Evaluation of an isomorphism of cohomological delta functors in degree `n`. -/
noncomputable def app (e : HomIso F G) (n : ℕ) : (F.F n).obj ≅ (G.F n).obj where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := app_hom_inv_id e n
  inv_hom_id := app_inv_hom_id e n

/-- The forward map of the degreewise isomorphism is the corresponding delta-functor component. -/
@[simp]
theorem app_hom (e : HomIso F G) (n : ℕ) :
    (app e n).hom = e.hom.app n := sorry

/-- The inverse map of the degreewise isomorphism is the corresponding delta-functor component. -/
@[simp]
theorem app_inv (e : HomIso F G) (n : ℕ) :
    (app e n).inv = e.inv.app n := sorry

end CategoryTheory.CohomologicalDeltaFunctor.Iso
