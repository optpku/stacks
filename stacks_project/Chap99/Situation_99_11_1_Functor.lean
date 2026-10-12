/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import stacks_project.Chap78.Remark_78_19_2_Quotient
public import stacks_project.Chap99.Situation_99_5_1_Fiber
public import stacks_project.Chap99.Situation_99_11_1_Pullback

/-!
# The relative Picard functor of a morphism of algebraic spaces

The unsheafified functor sends a scheme `T` over `B` to `Pic(X_T)`, and
`RelativePicard.functor` is its fppf sheafification on `(Sch/B)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack (SchemesOver fiber fiberMap)
open AlgebraicGeometry.AlgebraicSpace.PreRelation (schemesOverFppf)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The presheaf on schemes over `B` sending `T` to the Picard group of the fibre
`X_T = X ×_B T`. -/
def presheaf (f : X ⟶ B) : (SchemesOver B)ᵒᵖ ⥤ Type (u + 1) where
  obj σ := (fiber f σ.unop).PicardGroup
  map h := TypeCat.ofHom (picardPullback (fiberMap f h.unop))
  map_id := sorry
  map_comp := sorry

/-- Evaluation of the relative Picard presheaf at a scheme over `B`. -/
theorem presheaf_obj (f : X ⟶ B) (σ : SchemesOver B) :
    (presheaf f).obj (op σ) = (fiber f σ).PicardGroup := sorry

/-- The relative Picard functor is the fppf sheafification of `T ↦ Pic(X_T)`. -/
def functor (f : X ⟶ B) : Sheaf (schemesOverFppf B) (Type (u + 1)) :=
  (presheafToSheaf (schemesOverFppf B) (Type (u + 1))).obj (presheaf f)

/-- The underlying presheaf of `functor f` is the fppf sheafification of
`presheaf f`. -/
theorem functor_val (f : X ⟶ B) :
    (functor f).obj = (schemesOverFppf B).sheafify (presheaf f) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
