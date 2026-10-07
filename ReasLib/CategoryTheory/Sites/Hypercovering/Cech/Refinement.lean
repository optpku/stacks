module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology
public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Refinement

/-!
# Refinements and homotopy-invariant hypercovering Cech cohomology

Raw refinements induce maps of Cech complexes.  Homotopic raw refinements induce equal maps only
after taking cohomology, so the cohomology diagram descends to the opposite of the hypercovering
homotopy category while the complex-level map deliberately remains in the raw category.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory

open AlgebraicTopology
open Limits
open Opposite
open scoped CategoryTheory.SemiRepresentableFamily

namespace Hypercovering

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]
variable {X : C}

namespace Cech

/-- The morphism of Cech complexes induced by a raw refinement. -/
noncomputable def rawComplexMap
    {K L : RawRefinementCategory.{w} J X} (f : K ⟶ L)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    complex K.unop I ⟶ complex L.unop I :=
  complexMap f.unop I

/-- The map on Cech cohomology induced by a raw refinement. -/
noncomputable def rawCohomologyMap
    {K L : RawRefinementCategory.{w} J X} (f : K ⟶ L)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    cohomology K.unop I i ⟶ cohomology L.unop I i :=
  cohomologyMap f.unop I i

/-- The Cech cohomology map of an identity raw refinement is the identity. -/
theorem rawCohomologyMap_id
    (K : RawRefinementCategory.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    rawCohomologyMap (𝟙 K) I i = 𝟙 _ := sorry

/-- Cech cohomology maps respect composition of raw refinements. -/
theorem rawCohomologyMap_comp
    {K L M : RawRefinementCategory.{w} J X} (f : K ⟶ L) (g : L ⟶ M)
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    rawCohomologyMap (f ≫ g) I i =
      rawCohomologyMap f I i ≫ rawCohomologyMap g I i := sorry

/-- Zigzag-homotopic raw refinements induce the same map on Cech cohomology. -/
@[stacks 01GZ "homotopy invariance of hypercovering Cech cohomology"]
theorem rawCohomologyMap_eq_of_homotopic
    {K L : RawRefinementCategory.{w} J X} (f g : K ⟶ L)
    (h : SimplicialObject.Homotopic
      (Hypercovering.Hom.toSimplicial f.unop)
      (Hypercovering.Hom.toSimplicial g.unop))
    (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    rawCohomologyMap f I i = rawCohomologyMap g I i := sorry

/-- The coefficient-valued Cech diagram on fixed-target refinements, obtained by pulling back
the canonical presheaf-target diagram along the represented-target refinement functor. -/
@[stacks 01GZ "fixed-target coefficient-valued refinement diagram"]
noncomputable def refinementDiagram (X : C) (i : ℕ) :
    RefinementCategory.{w} J X ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) :=
  RefinementCategory.toPresheafTarget.{w, v, u} (J := J) (X := X) ⋙
    HypercoveringOf.Cech.refinementDiagram (uliftYoneda.{w}.obj X) i

/-- At a fixed-target refinement stage, the pulled-back diagram is its Cech cohomology functor
of the coefficient sheaf. -/
@[simp]
theorem refinementDiagram_obj
    (X : C) (i : ℕ) (K : RefinementCategory.{w} J X) :
    (refinementDiagram X i).obj K = cohomologyInCoefficients K.unop.as i := sorry

/-- The degree-`i` Cech cohomology diagram on fixed-target refinements, obtained by evaluating
the coefficient-valued refinement diagram. -/
noncomputable def refinementFunctor
    (X : C) (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    RefinementCategory.{w} J X ⥤ AddCommGrpCat.{max u v w} :=
  refinementDiagram X i ⋙ (evaluation _ _).obj I

/-- Evaluating the coefficient-valued fixed-target diagram recovers the fixed-coefficient
refinement functor. -/
theorem refinementDiagram_evaluation
    (X : C) (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ) :
    refinementDiagram X i ⋙ (evaluation _ _).obj I =
      refinementFunctor X I i := sorry

/-- Evaluating the quotient Cech diagram at a hypercovering gives its Cech cohomology. -/
@[simp]
theorem refinementFunctor_obj
    (X : C) (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    (K : RefinementCategory.{w} J X) :
    (refinementFunctor X I i).obj K =
      cohomology K.unop.as I i := sorry

/-- On a represented refinement class, the quotient Cech diagram uses the raw cohomology map. -/
@[simp]
theorem refinementFunctor_map_quotient
    (X : C) (I : Sheaf J AddCommGrpCat.{max w v}) (i : ℕ)
    {K L : RawRefinementCategory.{w} J X} (f : K ⟶ L) :
    (refinementFunctor X I i).map (refinementQuotient.map f) =
      rawCohomologyMap f I i := sorry

end Cech

end Hypercovering

end CategoryTheory
