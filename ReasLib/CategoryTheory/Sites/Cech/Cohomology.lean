module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import ReasLib.CategoryTheory.Sites.Cech.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech cohomology functors

This leaf packages degreewise Cech cohomology as an additive functor. Its hypotheses do not
include exactness of products; that stronger assumption enters only when connecting morphisms are
assembled in `Cech.DeltaFunctor`.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe w vA uA v u

namespace CategoryTheory.Cech

variable {C : Type u} [Category.{v} C]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)
variable [HasProducts.{w} A]

/-- The additive degree-`n` Cech cohomology functor for `A`-valued presheaves. -/
@[stacks 03AR "degreewise Cech cohomology functor"]
noncomputable abbrev cohomologyFunctor (n : ℕ) :
    (Cᵒᵖ ⥤ A) ⥤+ A :=
  AdditiveFunctor.of (cechComplexOnPresheaves U family ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n)

/-- The underlying functor of degree-`n` Cech cohomology is homology of the Cech-complex
functor. -/
@[simp]
theorem cohomologyFunctor_obj (n : ℕ) :
    (cohomologyFunctor U family n).obj = cechComplexOnPresheaves U family ⋙
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n := sorry

/-- Evaluating degree-`n` Cech cohomology at a presheaf gives its Cech cohomology object. -/
@[simp]
theorem cohomologyFunctor_obj_obj (n : ℕ) (F : Cᵒᵖ ⥤ A) :
    ((cohomologyFunctor U family n).obj).obj F = cechCohomology U family F n := sorry

/-- A morphism of presheaves induces the homology map of the corresponding Cech-complex
morphism. -/
@[simp]
theorem cohomologyFunctor_map {F G : Cᵒᵖ ⥤ A} (n : ℕ) (f : F ⟶ G) :
    (cohomologyFunctor U family n).obj.map f =
      HomologicalComplex.homologyMap ((cechComplexOnPresheaves U family).map f) n := sorry

end CategoryTheory.Cech
