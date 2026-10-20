module

public import ReasLib.CategoryTheory.Sites.Hypercovering.HomotopyCategory
public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Augmentation
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Refinement
public import ReasLib.CategoryTheory.Sites.Hypercovering.Product
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed-target refinements as presheaf-target refinements

The canonical functor from fixed-target hypercoverings to hypercoverings of the represented
target preserves simplicial homotopy.  It therefore descends once to homotopy categories, and
after taking opposites supplies the reusable bridge between the two refinement categories.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

open Limits Opposite

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C} {X : C}

/-- The raw refinement category: arrows are reversed strict morphisms of hypercoverings. -/
abbrev RawRefinementCategory (J : GrothendieckTopology C) (X : C) :=
  (Hypercovering.{w} J X)ᵒᵖ

/-- Section 25.10 (Tag 01GZ): the refinement index category of hypercoverings, with morphisms
taken up to zigzag simplicial homotopy. -/
@[stacks 01GZ "hypercovering refinement category"]
abbrev RefinementCategory (J : GrothendieckTopology C) (X : C) :=
  (HomotopyCategory.{v, u, w} J X)ᵒᵖ

/-- The quotient functor from raw refinements to homotopy classes of refinements. -/
abbrev refinementQuotient :
    RawRefinementCategory.{w} J X ⥤ RefinementCategory.{w} J X :=
  (HomotopyCategory.quotient (J := J) (X := X)).op

/-- A fixed-target hypercovering as an object of its refinement category. -/
@[stacks 01GZ "fixed-target refinement object"]
abbrev refinementObject (K : Hypercovering.{w} J X) :
    RefinementCategory.{w} J X :=
  op ((HomotopyCategory.quotient (J := J) (X := X)).obj K)

/-- A fixed-target hypercovering morphism in the contravariant refinement direction. -/
@[stacks 01GZ "fixed-target refinement map"]
abbrev refinementMap {K L : Hypercovering.{w} J X} (f : K ⟶ L) :
    refinementObject L ⟶ refinementObject K :=
  ((HomotopyCategory.quotient (J := J) (X := X)).map f).op

/-- The homotopy refinement category is filtered: products give common refinement objects, and
homotopy refinement equalizes parallel arrows. -/
@[stacks 01GZ "filtered hypercovering refinement category"]
instance refinementCategoryIsFiltered :
    IsFiltered (RefinementCategory.{w} J X) := sorry

namespace RawRefinement

/-- A raw refinement, viewed as its underlying simplicial morphism in the contravariant
refinement direction. -/
abbrev toSimplicial
    {K L : RawRefinementCategory.{w} J X} (f : K ⟶ L) :
    L.unop.toSimplicialObject ⟶ K.unop.toSimplicialObject :=
  Hom.toSimplicial f.unop

end RawRefinement

namespace HomotopyCategory

/-- The fixed-target functor followed by the presheaf-target homotopy quotient. -/
abbrev toPresheafTargetQuotient :
    Hypercovering.{w} J X ⥤
      HypercoveringOf.HomotopyCategory J (uliftYoneda.{w}.obj X) :=
  Hypercovering.toPresheafTargetFunctor ⋙
    HypercoveringOf.HomotopyCategory.quotient

/-- Homotopic fixed-target maps have equal images in the presheaf-target homotopy category. -/
theorem toPresheafTargetQuotient_map_eq_of_homotopic
    {K L : Hypercovering.{w} J X} (f g : K ⟶ L)
    (h : SimplicialObject.Homotopic (Hom.toSimplicial f) (Hom.toSimplicial g)) :
    toPresheafTargetQuotient.map f = toPresheafTargetQuotient.map g := sorry

/-- The represented-target functor descended to homotopy categories. -/
@[stacks 01GZ "represented-target homotopy functor"]
noncomputable def toPresheafTarget :
    Hypercovering.HomotopyCategory.{v, u, w} J X ⥤
      HypercoveringOf.HomotopyCategory J (uliftYoneda.{w}.obj X) :=
  CategoryTheory.Quotient.lift
    (Hypercovering.homotopyRel (J := J) (X := X))
    toPresheafTargetQuotient
    (fun _ _ f g h ↦ toPresheafTargetQuotient_map_eq_of_homotopic f g h)

/-- Descending to the homotopy category commutes with the represented-target functor. -/
theorem quotient_comp_toPresheafTarget :
    Hypercovering.HomotopyCategory.quotient (J := J) (X := X) ⋙
        toPresheafTarget (J := J) (X := X) =
      Hypercovering.toPresheafTargetFunctor (J := J) (X := X) ⋙
        HypercoveringOf.HomotopyCategory.quotient
          (J := J) (𝒢 := uliftYoneda.{w}.obj X) := sorry

end HomotopyCategory

namespace RefinementCategory

/-- The represented-target functor between homotopy refinement categories. -/
@[stacks 01GZ "represented-target refinement functor"]
noncomputable def toPresheafTarget :
    Hypercovering.RefinementCategory.{w} J X ⥤
      HypercoveringOf.RefinementCategory J (uliftYoneda.{w}.obj X) :=
  HomotopyCategory.toPresheafTarget.op

/-- The refinement bridge sends a represented fixed-target stage to the corresponding
presheaf-target stage. -/
@[simp]
theorem toPresheafTarget_obj
    (K : Hypercovering.RefinementCategory.{w} J X) :
    (toPresheafTarget (J := J) (X := X)).obj K =
      HypercoveringOf.refinementObject K.unop.as.toPresheafTarget := sorry

/-- On a represented strict refinement, the refinement bridge is the presheaf-target
refinement induced by the same simplicial map. -/
@[simp]
theorem toPresheafTarget_map_quotient
    {K L : Hypercovering.RawRefinementCategory.{w} J X} (f : K ⟶ L) :
    (toPresheafTarget (J := J) (X := X)).map
        (Hypercovering.refinementQuotient.map f) =
      HypercoveringOf.refinementMap (Hom.toPresheafTarget f.unop) := sorry

end RefinementCategory

end CategoryTheory.Hypercovering
