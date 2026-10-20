/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Refinement
public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.DerivedComparison
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.ComparisonData

/-!
# Comparison and spectral-sequence systems for hypercovering Čech cohomology

The comparison is a natural transformation in both the hypercovering refinement and the
coefficient sheaf.  The spectral sequence is packaged as a bifunctor rather than as unrelated
pointwise choices; its `E₂` identification is natural in both variables and its target is tied to
the infinity page by the reusable first-quadrant abutment predicate.
-/

@[expose] public section

noncomputable section

universe d w v u

namespace CategoryTheory

open Opposite

namespace Hypercovering.Cech

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [Limits.HasPullbacks C]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]

/-- The refinement diagram of fixed-target Cech cohomology functors. -/
abbrev refinementComparisonSource (X : C) (i : ℕ) :
    Hypercovering.RefinementCategory.{w} J X ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) :=
  refinementDiagram (J := J) X i

/-- The constant refinement diagram with value objectwise sheaf cohomology. -/
abbrev refinementComparisonTarget (X : C) (i : ℕ) :
    Hypercovering.RefinementCategory.{w} J X ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) :=
  Hypercovering.RefinementCategory.toPresheafTarget (J := J) (X := X) ⋙
    HypercoveringOf.Cech.refinementComparisonTarget
      (J := J) (uliftYoneda.{w}.obj X) i

/-- A degreewise comparison for one fixed-target hypercovering, natural in the coefficient
sheaf. -/
@[stacks 01GY "degree comparison datum"]
abbrev DegreeComparison (K : Hypercovering.{w} J X) (i : ℕ) :=
  HypercoveringOf.Cech.DegreeComparison K.toPresheafTarget i

/-- Lemma 25.5.3 (Tag 01GY): a comparison from hypercovering Cech cohomology to objectwise sheaf
cohomology, natural in both the refinement class and the coefficient sheaf. -/
@[stacks 01GY "refinement-natural comparison datum"]
abbrev RefinementComparison (X : C) (i : ℕ) :=
  refinementComparisonSource (J := J) X i ⟶
    refinementComparisonTarget (J := J) X i

namespace RefinementComparison

/-- Pull a presheaf-target refinement comparison back to fixed-target hypercoverings along the
represented-target refinement functor. -/
@[stacks 01GY "represented-target refinement comparison"]
noncomputable def pullback
    {X : C} {i : ℕ}
    (alpha : HypercoveringOf.Cech.RefinementComparison
      (J := J) (uliftYoneda.{w}.obj X) i) :
    RefinementComparison (J := J) X i :=
  Functor.whiskerLeft
    (Hypercovering.RefinementCategory.toPresheafTarget (J := J) (X := X)) alpha

end RefinementComparison

section Derived

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]
variable {X : C}
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J
      (uliftYoneda.{w}.obj X)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf J AddCommGrpCat.{max w v}))]

namespace DerivedComparison

/-- The generic degree system specialized to the represented target of a fixed-target
hypercovering. -/
@[stacks 01GY "degreewise comparison system"]
abbrev DegreeSystem (K : Hypercovering.{w} J X) :=
  HypercoveringOf.Cech.DerivedComparison.DegreeSystem K.toPresheafTarget

namespace DegreeSystem

/-- The ordinary fixed-target degree comparison obtained from the represented-target system. -/
noncomputable abbrev degreeComparison {K : Hypercovering.{w} J X}
    (S : DegreeSystem K) (i : ℕ) : DegreeComparison K i :=
  HypercoveringOf.Cech.DerivedComparison.DegreeSystem.degreeComparison S i

/-- The degree-zero comparison of a normalized fixed-target system is invertible at every
coefficient sheaf. -/
theorem degreeComparison_zero_isIso_app {K : Hypercovering.{w} J X}
    (S : DegreeSystem K) (I : Sheaf J AddCommGrpCat.{max w v}) :
    IsIso ((S.degreeComparison 0).app I) := sorry

end DegreeSystem

/-- Lemma 25.5.3 (01GY), degreewise clause: one normalized derived comparison supplies fixed
ordinary comparisons simultaneously in every nonnegative degree. -/
@[stacks 01GY "degreewise comparison"]
theorem degreeSystem_nonempty (K : Hypercovering.{w} J X) :
    Nonempty (DegreeSystem K) := sorry

end DerivedComparison

namespace RefinementComparison

/-- Refinement-natural comparisons in every degree, all induced by one explicit derived
comparison system at each hypercovering stage. -/
@[stacks 01GY "derived refinement comparison"]
structure Derived where
  /-- The generic normalized degree system at the represented image of each fixed-target
  refinement stage. -/
  stage (K : Hypercovering.RefinementCategory.{w} J X) :
    HypercoveringOf.Cech.DerivedComparison.DegreeSystem
      ((Hypercovering.RefinementCategory.toPresheafTarget
        (J := J) (X := X)).obj K).unop.as
  /-- The comparison in each degree, natural in refinements and coefficient sheaves. -/
  hom (i : ℕ) : RefinementComparison (J := J) X i
  /-- Every refinement-natural component is induced by the same derived stage comparison. -/
  app_eq (K : Hypercovering.RefinementCategory.{w} J X) (i : ℕ) :
    (hom i).app K = (stage K).degreeComparison i

namespace Derived

/-- The pulled-back comparison at a fixed refinement stage is the degree comparison selected by
the generic derived system at its represented image. -/
theorem pullback_app_eq
    (S : HypercoveringOf.Cech.RefinementComparison.Derived
      (J := J) (G := uliftYoneda.{w}.obj X))
    (K : Hypercovering.RefinementCategory.{w} J X) (i : ℕ) :
    (RefinementComparison.pullback (S.hom i)).app K =
      (S.stage ((Hypercovering.RefinementCategory.toPresheafTarget
        (J := J) (X := X)).obj K)).degreeComparison i := sorry

/-- Pull a generic derived refinement comparison system for the represented target back to the
fixed-target refinement category. -/
@[stacks 01GY "represented-target derived comparison"]
noncomputable def pullback
    (S : HypercoveringOf.Cech.RefinementComparison.Derived
      (J := J) (G := uliftYoneda.{w}.obj X)) :
    RefinementComparison.Derived (J := J) (X := X) where
  stage K := S.stage
    ((Hypercovering.RefinementCategory.toPresheafTarget
      (J := J) (X := X)).obj K)
  hom i := RefinementComparison.pullback (S.hom i)
  app_eq K i := pullback_app_eq S K i

end Derived

/-- One derived comparison system induces all degreewise comparisons compatibly with every
refinement. -/
@[stacks 01GY "derived refinement comparison existence"]
theorem derived_nonempty :
    Nonempty (Derived (J := J) (X := X)) := sorry

end RefinementComparison

end Derived

/-- Lemma 25.5.3 (Tag 01GY): a first-quadrant hypercovering spectral-sequence system, functorial
contravariantly in the hypercovering and covariantly in the coefficient sheaf. -/
@[stacks 01GY "spectral sequence system"]
structure SpectralSequenceSystem (X : C) where
  /-- The bifunctorial family of first-quadrant spectral sequences. -/
  functor :
    (Hypercovering.{w} J X)ᵒᵖ ⥤
      Sheaf J AddCommGrpCat.{max w v} ⥤
        E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v w}
  /-- The `E₂` page is Čech cohomology with coefficients in the universe-raised objectwise
  cohomology presheaf. -/
  pageTwoIso :
    ∀ (K : Hypercovering.{w} J X)
      (I : Sheaf J AddCommGrpCat.{max w v}) (p q : ℕ),
      (((functor.obj (op K)).obj I).page 2 le_rfl).X (p, q) ≅
        presheafCohomology K
          (Sheaf.uliftCohomologyPresheaf J I q) p
  /-- The `E₂` identification is natural in the coefficient sheaf. -/
  pageTwo_natural_coefficients :
    ∀ (K : Hypercovering.{w} J X)
      {I I' : Sheaf J AddCommGrpCat.{max w v}} (φ : I ⟶ I') (p q : ℕ),
      (((functor.obj (op K)).map φ).hom 2 le_rfl).f (p, q) ≫
          (pageTwoIso K I' p q).hom =
        (pageTwoIso K I p q).hom ≫
          (presheafCohomologyInCoefficients K p).map
            ((Sheaf.uliftCohomologyPresheafFunctor J q).map φ)
  /-- The `E₂` identification is natural under contravariant hypercovering refinement. -/
  pageTwo_natural_refinements :
    ∀ {K L : Hypercovering.{w} J X} (f : K ⟶ L)
      (I : Sheaf J AddCommGrpCat.{max w v}) (p q : ℕ),
      (((functor.map f.op).app I).hom 2 le_rfl).f (p, q) ≫
          (pageTwoIso K I p q).hom =
        (pageTwoIso L I p q).hom ≫
          presheafCohomologyMap f
            (Sheaf.uliftCohomologyPresheaf J I q) p
  /-- Each spectral sequence abuts to objectwise sheaf cohomology over the fixed target. -/
  abuts :
    ∀ (K : Hypercovering.{w} J X)
      (I : Sheaf J AddCommGrpCat.{max w v}),
      E₂CohomologicalSpectralSequenceNat.AbutsTo
        ((functor.obj (op K)).obj I)
        (fun n ↦ (Sheaf.cohomologyOverObjectFunctor J X n).obj I)

namespace SpectralSequenceSystem

/-- Pull back the generic presheaf-target spectral-sequence bifunctor along the represented-target
functor on fixed-target hypercoverings. -/
noncomputable def pullbackFunctor
    {X : C}
    (S : HypercoveringOf.Cech.SpectralSequenceSystem
      (J := J) (uliftYoneda.{w}.obj X)) :
    (Hypercovering.{w} J X)ᵒᵖ ⥤
      Sheaf J AddCommGrpCat.{max w v} ⥤
        E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v w} :=
  Hypercovering.toPresheafTargetFunctor.op ⋙ S.functor

/-- The pulled-back second-page identification at a fixed-target hypercovering. -/
noncomputable def pullbackPageTwoIso
    {X : C}
    (S : HypercoveringOf.Cech.SpectralSequenceSystem
      (J := J) (uliftYoneda.{w}.obj X))
    (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p q : ℕ) :
    ((((pullbackFunctor S).obj (op K)).obj I).page 2 le_rfl).X (p, q) ≅
      presheafCohomology K (Sheaf.uliftCohomologyPresheaf J I q) p :=
  S.pageTwoIso K.toPresheafTarget I p q

/-- The pulled-back second-page identification is natural in the coefficient sheaf. -/
theorem pullbackPageTwo_natural_coefficients
    {X : C}
    (S : HypercoveringOf.Cech.SpectralSequenceSystem
      (J := J) (uliftYoneda.{w}.obj X))
    (K : Hypercovering.{w} J X)
    {I I' : Sheaf J AddCommGrpCat.{max w v}} (phi : I ⟶ I') (p q : ℕ) :
    ((((pullbackFunctor S).obj (op K)).map phi).hom 2 le_rfl).f (p, q) ≫
        (pullbackPageTwoIso S K I' p q).hom =
      (pullbackPageTwoIso S K I p q).hom ≫
        (presheafCohomologyInCoefficients K p).map
          ((Sheaf.uliftCohomologyPresheafFunctor J q).map phi) := sorry

/-- The pulled-back second-page identification is natural under fixed-target refinements. -/
theorem pullbackPageTwo_natural_refinements
    {X : C}
    (S : HypercoveringOf.Cech.SpectralSequenceSystem
      (J := J) (uliftYoneda.{w}.obj X))
    {K L : Hypercovering.{w} J X} (f : K ⟶ L)
    (I : Sheaf J AddCommGrpCat.{max w v}) (p q : ℕ) :
    ((((pullbackFunctor S).map f.op).app I).hom 2 le_rfl).f (p, q) ≫
        (pullbackPageTwoIso S K I p q).hom =
      (pullbackPageTwoIso S L I p q).hom ≫
        presheafCohomologyMap f
          (Sheaf.uliftCohomologyPresheaf J I q) p := sorry

/-- The pulled-back spectral sequence abuts to objectwise cohomology over the represented
target. -/
theorem pullback_abuts
    {X : C}
    (S : HypercoveringOf.Cech.SpectralSequenceSystem
      (J := J) (uliftYoneda.{w}.obj X))
    (K : Hypercovering.{w} J X)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    E₂CohomologicalSpectralSequenceNat.AbutsTo
      (((pullbackFunctor S).obj (op K)).obj I)
      (fun n ↦ (Sheaf.cohomologyOverObjectFunctor J X n).obj I) := sorry

/-- Specialize a generic spectral-sequence system over a representable presheaf target to the
corresponding fixed-target hypercoverings. -/
@[stacks 01GY "represented-target spectral sequence"]
noncomputable def pullback
    {X : C}
    (S : HypercoveringOf.Cech.SpectralSequenceSystem
      (J := J) (uliftYoneda.{w}.obj X)) :
    SpectralSequenceSystem (J := J) X where
  functor := pullbackFunctor S
  pageTwoIso := pullbackPageTwoIso S
  pageTwo_natural_coefficients := pullbackPageTwo_natural_coefficients S
  pageTwo_natural_refinements := pullbackPageTwo_natural_refinements S
  abuts := pullback_abuts S

end SpectralSequenceSystem

/-- Lemma 25.5.3 (Tag 01GY), spectral-sequence clause: there is a bifunctorial first-quadrant
spectral-sequence system with the canonical Čech `E₂` page and objectwise-cohomology abutment. -/
@[stacks 01GY "spectral sequence"]
theorem spectralSequenceSystem_nonempty (X : C) :
    Nonempty (SpectralSequenceSystem (J := J) X) := sorry

end Hypercovering.Cech

end CategoryTheory
