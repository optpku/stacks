/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import ReasLib.CategoryTheory.Sites.Cohomology.Terminal
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.DerivedComparison
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Refinement
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison systems for presheaf-target hypercoverings

The Cech-to-Ext comparison is a natural transformation in the coefficient sheaf.  The associated
spectral sequences form a bifunctor, contravariant in the hypercovering and covariant in the
coefficient sheaf; their second pages use the topology-independent additive-presheaf Cech owner.
-/

@[expose] public section

noncomputable section

universe d w v u

namespace CategoryTheory.HypercoveringOf.Cech

open Opposite

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
variable {G : Cᵒᵖ ⥤ Type (max w v)}

/-- Presheaf-target hypercovering Cech cohomology as a functor of the coefficient sheaf. -/
abbrev degreeComparisonSource (K : HypercoveringOf.{w} J G) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w} :=
  cohomologyInCoefficients K i

/-- Cohomology over the target presheaf as a functor of the coefficient sheaf. -/
abbrev degreeComparisonTarget (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w} :=
  Sheaf.cohomologyOverPresheafFunctor.{max u v w, w, v, u} J G i

/-- A coefficient-natural degreewise comparison from the Cech cohomology of `K` to cohomology
over its target presheaf. The primary comparison lives in `D⁺`; this is its degree-`i`
interface. -/
@[stacks 09VX "degree comparison datum"]
abbrev DegreeComparison (K : HypercoveringOf.{w} J G) (i : ℕ) :=
  degreeComparisonSource.{w, v, u} K i ⟶
    degreeComparisonTarget.{w, v, u} (J := J) G i

/-- The constant refinement diagram with value cohomology over the target presheaf. -/
abbrev refinementComparisonTarget
    (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :
    HypercoveringOf.RefinementCategory J G ⥤
      (Sheaf J AddCommGrpCat.{max w v} ⥤ AddCommGrpCat.{max u v w}) :=
  (Functor.const (HypercoveringOf.RefinementCategory J G)).obj
    (degreeComparisonTarget (J := J) G i)

/-- Lemma 25.6.4 (Tag 09VX): a Cech-to-presheaf-cohomology comparison natural in both
refinement classes and coefficient sheaves. -/
@[stacks 09VX "refinement-natural comparison datum"]
abbrev RefinementComparison
    (G : Cᵒᵖ ⥤ Type (max w v)) (i : ℕ) :=
  refinementDiagram G i ⟶ refinementComparisonTarget (J := J) G i

section Derived

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J
      G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf J AddCommGrpCat.{max w v}))]

namespace DerivedComparison

/-- One derived comparison together with explicit source and target homology identifications in
every nonnegative degree. -/
@[stacks 09VX "degreewise comparison system"]
structure DegreeSystem (K : HypercoveringOf.{w} J G) where
  /-- The comparison in the bounded-below derived category. -/
  comparison : DerivedComparison K
  /-- Homology of the extended Cech source is identified with ordinary Cech cohomology. -/
  sourceIso (i : ℕ) :
    (derivedSource K ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} i) ≅
      degreeComparisonSource K i
  /-- Homology of the derived target is identified with presheaf cohomology. -/
  targetIso (i : ℕ) :
    (derivedTarget (J := J) (G := G) ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} i) ≅
      degreeComparisonTarget (J := J) G i

namespace DegreeSystem

/-- The ordinary degreewise comparison obtained from the fixed derived comparison and fixed
homology identifications. -/
noncomputable def degreeComparison {K : HypercoveringOf.{w} J G}
    (S : DegreeSystem K) (i : ℕ) : DegreeComparison K i :=
  (S.sourceIso i).inv ≫ S.comparison.homology i ≫ (S.targetIso i).hom

/-- The degree-zero comparison of a normalized system is invertible at every coefficient
sheaf. -/
theorem degreeComparison_zero_isIso_app {K : HypercoveringOf.{w} J G}
    (S : DegreeSystem K) (I : Sheaf J AddCommGrpCat.{max w v}) :
    IsIso ((S.degreeComparison 0).app I) := sorry

end DegreeSystem

/-- Lemma 25.6.4 (09VX), degreewise clause: one normalized derived comparison supplies fixed
ordinary comparisons simultaneously in every nonnegative degree. -/
@[stacks 09VX "degreewise comparison"]
theorem degreeSystem_nonempty (K : HypercoveringOf.{w} J G) :
    Nonempty (DegreeSystem K) := sorry

end DerivedComparison

namespace RefinementComparison

/-- Refinement-natural comparisons in every degree, all induced by one explicit derived
comparison system at each hypercovering stage. -/
@[stacks 09VX "derived refinement comparison"]
structure Derived where
  /-- The normalized derived comparison and homology identifications at each refinement stage. -/
  stage (K : HypercoveringOf.RefinementCategory J G) :
    DerivedComparison.DegreeSystem K.unop.as
  /-- The comparison in each degree, natural in refinements and coefficient sheaves. -/
  hom (i : ℕ) : RefinementComparison (J := J) G i
  /-- Every refinement-natural component is induced by the same derived stage comparison. -/
  app_eq (K : HypercoveringOf.RefinementCategory J G) (i : ℕ) :
    (hom i).app K = (stage K).degreeComparison i

/-- One derived comparison system induces all degreewise comparisons compatibly with every
refinement. -/
@[stacks 09VX "derived refinement comparison existence"]
theorem derived_nonempty :
    Nonempty (Derived (J := J) (G := G)) := sorry

end RefinementComparison

end Derived

/-- A functorial first-quadrant spectral-sequence system for all hypercoverings of a fixed
presheaf target. -/
@[stacks 09VX "spectral sequence system"]
structure SpectralSequenceSystem (G : Cᵒᵖ ⥤ Type (max w v)) where
  /-- The spectral sequence is contravariant in augmentation-preserving hypercovering maps and
  covariant in coefficient morphisms. -/
  functor :
    (HypercoveringOf.{w} J G)ᵒᵖ ⥤
      Sheaf J AddCommGrpCat.{max w v} ⥤
        E₂CohomologicalSpectralSequenceNat AddCommGrpCat.{max u v w}
  /-- The second page is product-sections Cech cohomology with coefficients in the canonical
  cohomology presheaf. -/
  pageTwoIso :
    ∀ (K : HypercoveringOf.{w} J G)
      (I : Sheaf J AddCommGrpCat.{max w v}) (p q : ℕ),
      (((functor.obj (op K)).obj I).page 2 le_rfl).X (p, q) ≅
        presheafCohomology K (Sheaf.uliftCohomologyPresheaf J I q) p
  /-- The second-page identification is natural in the coefficient sheaf. -/
  pageTwo_natural_coefficients :
    ∀ (K : HypercoveringOf.{w} J G)
      {I I' : Sheaf J AddCommGrpCat.{max w v}} (φ : I ⟶ I') (p q : ℕ),
      (((functor.obj (op K)).map φ).hom 2 le_rfl).f (p, q) ≫
          (pageTwoIso K I' p q).hom =
        (pageTwoIso K I p q).hom ≫
          (presheafCohomologyInCoefficients K p).map
            ((Sheaf.uliftCohomologyPresheafFunctor J q).map φ)
  /-- The second-page identification is natural under contravariant hypercovering maps. -/
  pageTwo_natural_hypercoverings :
    ∀ {K L : HypercoveringOf.{w} J G} (f : K ⟶ L)
      (I : Sheaf J AddCommGrpCat.{max w v}) (p q : ℕ),
      (((functor.map f.op).app I).hom 2 le_rfl).f (p, q) ≫
          (pageTwoIso K I p q).hom =
        (pageTwoIso L I p q).hom ≫
          presheafCohomologyMap f (Sheaf.uliftCohomologyPresheaf J I q) p
  /-- Each spectral sequence abuts to `Ext` cohomology over the target presheaf. -/
  abuts :
    ∀ (K : HypercoveringOf.{w} J G)
      (I : Sheaf J AddCommGrpCat.{max w v}),
      E₂CohomologicalSpectralSequenceNat.AbutsTo
        ((functor.obj (op K)).obj I)
        (fun n ↦
          (Sheaf.cohomologyOverPresheafFunctor.{max u v w, w, v, u} J G n).obj I)

namespace SpectralSequenceSystem

/-- Lemma 25.6.5 (09VY), reusable terminal-target specialization: a presheaf-target
hypercovering spectral sequence abuts to ordinary global sheaf cohomology when its target is the
terminal presheaf. -/
@[stacks 09VY "global cohomology abutment"]
theorem abutsGlobal
    (S : SpectralSequenceSystem.{w, v, u} (J := J) (Presheaf.terminal C))
    (K : HypercoveringOf.Terminal.{w} J)
    (I : Sheaf J AddCommGrpCat.{max w v}) :
    E₂CohomologicalSpectralSequenceNat.AbutsTo
      ((S.functor.obj (op K)).obj I)
      (fun n ↦
        (Sheaf.functorH.{max u v w, max w v, v, u} J n).obj I) := sorry

end SpectralSequenceSystem

/-- Lemma 25.6.4 (09VX), spectral-sequence clause: a bifunctorial hypercovering spectral
sequence system exists once its target presheaf is supplied. -/
@[stacks 09VX "spectral sequence"]
theorem spectralSequenceSystem_nonempty
    (G : Cᵒᵖ ⥤ Type (max w v)) :
    Nonempty (SpectralSequenceSystem.{w, v, u} (J := J) G) := sorry

end CategoryTheory.HypercoveringOf.Cech
