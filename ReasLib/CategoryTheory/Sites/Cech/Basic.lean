module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Čech complexes on slice categories

This module owns the coefficient-independent restriction of presheaves to an ordinary slice,
and the additive Čech-complex specialization for an indexed family in that slice.  The
underlying Čech construction remains Mathlib's `cechComplexFunctor`.
-/

@[expose] public section

noncomputable section

universe w v' u' v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C]

section

variable {U : C} [HasFiniteProducts (Over U)]

/-- The index type of degree-`n` iterated Čech intersections of a formal coproduct in
`Over U`. -/
abbrev cechCoverIntersectionIndex (cover : FormalCoproduct (Over U)) (n : ℕ) :=
  (cover.cech.obj (op (SimplexCategory.mk n))).I

/-- The underlying object of `C` of a degree-`n` Čech intersection in `Over U`. -/
abbrev cechCoverIntersectionObject (cover : FormalCoproduct (Over U)) (n : ℕ)
    (i : cechCoverIntersectionIndex cover n) : C :=
  ((cover.cech.obj (op (SimplexCategory.mk n))).obj i).left

end

section

variable {A : Type u'} [Category.{v'} A]

/-- Restriction of an `A`-valued presheaf on `C` to `Over U`, given by precomposition with
`(Over.forget U).op`. -/
abbrev restrictPresheafToOver (U : C) :
    (Cᵒᵖ ⥤ A) ⥤ ((Over U)ᵒᵖ ⥤ A) :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ A).obj (Over.forget U).op

/-- Restricting a presheaf to a slice is definitionally precomposition with the slice forgetful
functor. -/
@[simp]
theorem restrictPresheafToOver_obj (U : C) (F : Cᵒᵖ ⥤ A) :
    (restrictPresheafToOver U).obj F = (Over.forget U).op ⋙ F := sorry

/-- Evaluating a presheaf restricted to `Over U` at `V ⟶ U` evaluates the original presheaf at
`V`. -/
@[simp]
theorem restrictPresheafToOver_obj_obj (U : C) (F : Cᵒᵖ ⥤ A) (V : Over U) :
    ((restrictPresheafToOver U).obj F).obj (op V) = F.obj (op V.left) := sorry

/-- The map of a presheaf restricted to `Over U` is the map induced by the underlying slice
morphism. -/
@[simp]
theorem restrictPresheafToOver_obj_map
    (U : C) (F : Cᵒᵖ ⥤ A) {V W : Over U} (f : V ⟶ W) :
    ((restrictPresheafToOver U).obj F).map f.op = F.map f.left.op := sorry

/-- Restriction to a slice sends a natural transformation to its left whiskering by the slice
forgetful functor. -/
@[simp]
theorem restrictPresheafToOver_map
    (U : C) {F G : Cᵒᵖ ⥤ A} (α : F ⟶ G) :
    (restrictPresheafToOver U).map α = (Over.forget U).op.whiskerLeft α := sorry

/-- The component of a restricted natural transformation at a slice object is its original
component at the underlying object. -/
@[simp]
theorem restrictPresheafToOver_map_app
    (U : C) {F G : Cᵒᵖ ⥤ A} (α : F ⟶ G) (V : Over U) :
    ((restrictPresheafToOver U).map α).app (op V) = α.app (op V.left) := sorry

end

section Complex

variable {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w}

/-- The Čech complex of a presheaf with values in a preadditive category, for an indexed family
of arrows into `U`. -/
@[stacks 03AM]
abbrev cechComplex (family : ι → Over U) (F : Cᵒᵖ ⥤ A) :
    CochainComplex A ℕ :=
  (cechComplexFunctor family).obj ((restrictPresheafToOver U).obj F)

/-- The Čech-complex functor on presheaves valued in a preadditive category, associated to a family
in `Over U`. -/
@[stacks 03AP]
abbrev cechComplexOnPresheaves (family : ι → Over U) :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  restrictPresheafToOver U ⋙ cechComplexFunctor family

/-- Evaluating the Čech-complex functor on a presheaf gives its Čech complex. -/
@[simp]
theorem cechComplexOnPresheaves_obj
    (family : ι → Over U) (F : Cᵒᵖ ⥤ A) :
    (cechComplexOnPresheaves U family).obj F = cechComplex U family F := sorry

/-- In degree `p`, the Čech-complex functor is the product of values on the degree-`p`
iterated intersections of the family. -/
@[simp]
theorem cechComplexOnPresheaves_obj_X
    (family : ι → Over U) (F : Cᵒᵖ ⥤ A) (p : ℕ) :
    ((cechComplexOnPresheaves U family).obj F).X p =
      ∏ᶜ fun i : cechCoverIntersectionIndex (FormalCoproduct.mk _ family) p ↦
        F.obj (op (cechCoverIntersectionObject (FormalCoproduct.mk _ family) p i)) := sorry

/-- The morphism part of the Čech-complex functor is induced by restricting the natural
transformation to `Over U` and applying `cechComplexFunctor`. -/
@[simp]
theorem cechComplexOnPresheaves_map
    (family : ι → Over U) {F G : Cᵒᵖ ⥤ A} (α : F ⟶ G) :
    (cechComplexOnPresheaves U family).map α =
      (cechComplexFunctor family).map ((restrictPresheafToOver U).map α) := sorry

end Complex

section Cohomology

variable {A : Type u'} [Category.{v'} A] [Abelian A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w}
variable [HasProducts.{w} A]

/-- The degree-`i` Čech cohomology object of an `A`-valued presheaf for a family in `Over U`. -/
abbrev cechCohomology
    (family : ι → Over U) (F : Cᵒᵖ ⥤ A) (i : ℕ) : A :=
  (cechComplex U family F).homology i

/-- Čech cohomology is the degree-`i` homology object of the associated Čech complex. -/
@[simp]
theorem cechComplex_homology
    (family : ι → Over U) (F : Cᵒᵖ ⥤ A) (i : ℕ) :
    (cechComplex U family F).homology i = cechCohomology U family F i := sorry

/-- The degree-`i` homology of the Čech-complex functor is Čech cohomology. -/
@[simp]
theorem cechComplexOnPresheaves_obj_homology
    (family : ι → Over U) (F : Cᵒᵖ ⥤ A) (i : ℕ) :
    ((cechComplexOnPresheaves U family).obj F).homology i =
      cechCohomology U family F i := sorry

end Cohomology



end CategoryTheory
