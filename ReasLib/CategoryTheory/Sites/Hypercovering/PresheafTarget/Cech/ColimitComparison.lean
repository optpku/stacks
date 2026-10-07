module

public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Colimit
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.ComparisonData
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparisons out of presheaf-target hypercovering Cech colimits

A refinement-natural family of stage comparisons is a cocone on the coefficient-valued Cech
diagram. This leaf descends that family to the canonical colimit without burdening users of the
underlying colimit construction with derived-comparison dependencies.
-/

@[expose] public section

noncomputable section

universe w v u

namespace CategoryTheory.HypercoveringOf.Cech

open Limits

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

section Comparison

variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]

/-- Cohomology over the target presheaf, lifted functorially in the coefficient sheaf. -/
abbrev liftedTargetCohomology (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  degreeComparisonTarget (J := J) G i ⋙ universeLift.{max u v w}

/-- The constant refinement diagram with value lifted target cohomology. -/
abbrev liftedComparisonTarget (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    HypercoveringOf.RefinementCategory J G ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤
        AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)}) :=
  (Functor.const (HypercoveringOf.RefinementCategory J G)).obj
    (liftedTargetCohomology (J := J) G i)

/-- The lifted legs of a refinement-natural comparison satisfy the cocone equations. -/
theorem comparisonCocone_naturality {G : Cᵒᵖ ⥤ Type (max w v)} {i : ℕ}
    (c : RefinementComparison (J := J) G i)
    {K L : HypercoveringOf.RefinementCategory J G} (f : K ⟶ L) :
    (liftedDiagram.{w, v, u} (J := J) G i).map f ≫
        (coefficientLift.{w, v, u} (J := J)).map (c.app L) =
      (coefficientLift.{w, v, u} (J := J)).map (c.app K) ≫
        (liftedComparisonTarget.{w, v, u} (J := J) G i).map f := sorry

/-- The cocone from stagewise Cech cohomology functors to lifted cohomology over the target
presheaf. -/
noncomputable def comparisonCocone
    {G : Cᵒᵖ ⥤ Type (max w v)} {i : ℕ}
    (c : RefinementComparison (J := J) G i) :
    Cocone (liftedDiagram.{w, v, u} (J := J) G i) where
  pt := liftedTargetCohomology.{w, v, u} (J := J) G i
  ι :=
    { app K := (coefficientLift.{w, v, u} (J := J)).map (c.app K)
      naturality _ _ f :=
        comparisonCocone_naturality.{w, v, u} (J := J) c f }

/-- The comparison from presheaf-target hypercovering Cech cohomology to target cohomology,
natural in the coefficient sheaf. -/
@[stacks 09VZ "hypercovering colimit comparison"]
noncomputable def comparison
    {G : Cᵒᵖ ⥤ Type (max w v)} {i : ℕ}
    (c : RefinementComparison (J := J) G i) :
    cohomologyFunctor G i ⟶ liftedTargetCohomology (J := J) G i :=
  colimit.desc (liftedDiagram.{w, v, u} (J := J) G i)
    (comparisonCocone.{w, v, u} (J := J) c)

/-- The colimit comparison restricts at each refinement stage to the supplied comparison. -/
@[reassoc]
theorem ι_comp_comparison
    {G : Cᵒᵖ ⥤ Type (max w v)} {i : ℕ}
    (c : RefinementComparison (J := J) G i)
    (K : HypercoveringOf.RefinementCategory J G) :
    colimit.ι (liftedDiagram G i) K ≫ comparison c =
      coefficientLift.map (c.app K) := sorry

/-- At a fixed coefficient sheaf, the colimit comparison restricts to the supplied stagewise
comparison map. -/
@[reassoc]
theorem stageMap_comp_comparison_app
    {G : Cᵒᵖ ⥤ Type (max w v)} {i : ℕ}
    (c : RefinementComparison (J := J) G i) (K : HypercoveringOf J G)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    stageMap K I i ≫ (comparison c).app I =
      universeLift.{max u v w}.map
        ((c.app (HypercoveringOf.refinementObject K)).app I) := sorry

end Comparison

end CategoryTheory.HypercoveringOf.Cech
