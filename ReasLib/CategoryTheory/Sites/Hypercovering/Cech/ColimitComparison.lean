module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Colimit
public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.ComparisonData
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.ColimitComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparisons out of fixed-target hypercovering Cech colimits

This leaf builds the comparison from the fixed-target refinement colimit to objectwise sheaf
cohomology and packages the certified isomorphism. The underlying colimit remains available from
the lighter `Cech.Colimit` leaf.
-/

@[expose] public section

noncomputable section

universe d w v u

namespace CategoryTheory

open Limits

namespace Hypercovering.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasPullbacks C]

section Comparison

variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]

/-- Objectwise sheaf cohomology over `X`, lifted to the universe of the hypercovering
colimit. -/
abbrev liftedObjectwiseCohomology (X : C) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      AddCommGrpCat.{max (u + 1) (v + 1) (w + 1)} :=
  HypercoveringOf.Cech.liftedTargetCohomology
    (J := J) (uliftYoneda.{w}.obj X) i

/-- The lifted legs of a refinement-natural comparison satisfy the cocone equations. -/
theorem comparisonCocone_naturality {X : C} {i : ℕ}
    (c : RefinementComparison (J := J) X i)
    {K L : Hypercovering.RefinementCategory.{w} J X} (f : K ⟶ L) :
    (liftedDiagram X i).map f ≫
        HypercoveringOf.Cech.coefficientLift.map (c.app L) =
      HypercoveringOf.Cech.coefficientLift.map (c.app K) ≫
        ((Functor.const (Hypercovering.RefinementCategory.{w} J X)).obj
          (liftedObjectwiseCohomology (J := J) X i)).map f := sorry

/-- The cocone from stagewise Cech cohomology functors to lifted objectwise sheaf
cohomology. -/
noncomputable def comparisonCocone {X : C} {i : ℕ}
    (c : RefinementComparison (J := J) X i) :
    Cocone (liftedDiagram.{w, v, u} (J := J) X i) where
  pt := liftedObjectwiseCohomology (J := J) X i
  ι :=
    { app K := HypercoveringOf.Cech.coefficientLift.map (c.app K)
      naturality _ _ f := comparisonCocone_naturality c f }

/-- Theorem 25.10.1 (Tag 01H0): a refinement-natural stage comparison induces the concrete
map from hypercovering Cech cohomology to objectwise sheaf cohomology. -/
@[stacks 01H0 "comparison map"]
noncomputable def comparison {X : C} {i : ℕ}
    (c : RefinementComparison (J := J) X i) :
    cohomologyFunctor X i ⟶ liftedObjectwiseCohomology (J := J) X i :=
  colimit.desc (liftedDiagram X i) (comparisonCocone c)

/-- The colimit comparison restricts at each hypercovering stage to the supplied
refinement-natural comparison. -/
@[reassoc]
theorem ι_comp_comparison {X : C} {i : ℕ}
    (c : RefinementComparison (J := J) X i)
    (K : Hypercovering.RefinementCategory.{w} J X) :
    colimit.ι (liftedDiagram X i) K ≫ comparison c =
      HypercoveringOf.Cech.coefficientLift.map (c.app K) := sorry

/-- At a fixed coefficient sheaf, the colimit comparison restricts to the supplied comparison
at the stage represented by `K`. -/
@[reassoc]
theorem stageMap_comp_comparison_app {X : C} {i : ℕ}
    (c : RefinementComparison (J := J) X i) (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    stageMap K I i ≫ (comparison c).app I =
      HypercoveringOf.Cech.universeLift.{max u v w}.map
        ((c.app K.refinementObject).app I) := sorry

/-- Theorem 25.10.1 (Tag 01H0): a refinement-natural comparison whose induced map from
hypercovering Cech cohomology to objectwise sheaf cohomology is an isomorphism. -/
@[stacks 01H0 "certified comparison"]
structure Comparison
    [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
    [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]
    (X : C) (i : ℕ)
    [(Sheaf.CohomologyOverPresheaf.homFunctor J
        (uliftYoneda.{w}.obj X)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf J AddCommGrpCat.{max w v}))] where
  /-- The derived comparison at every stage, natural in refinements and coefficients. -/
  derived : RefinementComparison.Derived (J := J) (X := X)
  /-- The induced map out of the refinement colimit is an isomorphism. -/
  isIso : IsIso (comparison (derived.hom i))

attribute [instance] Comparison.isIso

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]

namespace Comparison

variable {X : C}
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J
      (uliftYoneda.{w}.obj X)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf J AddCommGrpCat.{max w v}))]

/-- The concrete map underlying a certified hypercovering comparison. -/
abbrev hom {i : ℕ} (c : Comparison (J := J) X i) :
    cohomologyFunctor X i ⟶ liftedObjectwiseCohomology (J := J) X i :=
  comparison (c.derived.hom i)

/-- The concrete isomorphism of coefficient functors supplied by a certified fixed-target
comparison. -/
noncomputable def iso {i : ℕ} (c : Comparison (J := J) X i) :
    cohomologyFunctor X i ≅ liftedObjectwiseCohomology (J := J) X i :=
  asIso c.hom

/-- A certified comparison restricts at every stage to its refinement-natural component. -/
@[reassoc]
theorem ι_comp_hom {i : ℕ} (c : Comparison (J := J) X i)
    (K : Hypercovering.RefinementCategory.{w} J X) :
    colimit.ι (liftedDiagram X i) K ≫ c.hom =
      HypercoveringOf.Cech.coefficientLift.map
        ((c.derived.hom i).app K) := sorry

end Comparison

variable (X : C)
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J
      (uliftYoneda.{w}.obj X)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf J AddCommGrpCat.{max w v}))]

/-- Theorem 25.10.1 (Tag 01H0): a certified comparison between hypercovering Cech
cohomology and objectwise sheaf cohomology exists in every nonnegative degree. -/
@[stacks 01H0 "comparison isomorphism"]
theorem comparison_nonempty (i : ℕ) :
    Nonempty (Comparison (J := J) X i) := sorry

/-- Forgetting stage compatibility from a certified comparison gives an isomorphism between
hypercovering Cech cohomology and objectwise sheaf cohomology as coefficient functors. -/
theorem isIsomorphic_objectwiseCohomology
    (i : ℕ) :
    IsIsomorphic (cohomologyFunctor X i)
      (liftedObjectwiseCohomology (J := J) X i) := sorry

end Comparison

end Hypercovering.Cech

end CategoryTheory
