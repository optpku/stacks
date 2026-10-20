module

public import ReasLib.CategoryTheory.Sites.Cohomology.Objectwise
public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology
public import ReasLib.CategoryTheory.Sites.Hypercovering.Presheaf.Augmentation
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.DerivedComparison

/-!
# Derived comparison for fixed-target hypercoverings

This leaf places the nonnegative Cech complex of a fixed-target hypercovering in the
bounded-below derived category and compares it with derived cohomology over the
universe-raised representable presheaf of the target.  Taking homology is exposed as a
separate degreewise API.
-/

@[expose] public section

noncomputable section

universe d w v u

namespace CategoryTheory.Hypercovering.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [Limits.HasPullbacks C]
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]
variable {X : C}
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J
      (uliftYoneda.{w}.obj X)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf J AddCommGrpCat.{max w v}))]

/-- The fixed-target Cech complex, extended by zero to a bounded-below complex and localized
in `D⁺(AddCommGrpCat)`, functorially in the coefficient sheaf. -/
@[stacks 01GY "derived comparison source"]
abbrev derivedSource (K : Hypercovering.{w} J X) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  HypercoveringOf.Cech.derivedSource K.toPresheafTarget

/-- Derived cohomology over the universe-raised representable presheaf of `X`, functorially
in the coefficient sheaf. -/
@[stacks 01GY "derived comparison target"]
abbrev derivedTarget :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  HypercoveringOf.Cech.derivedTarget (J := J) (G := uliftYoneda.{w}.obj X)

/-- A derived Cech-to-cohomology comparison for a fixed-target hypercovering, natural in the
coefficient sheaf. -/
@[stacks 01GY "derived comparison"]
abbrev DerivedComparison (K : Hypercovering.{w} J X) :=
  HypercoveringOf.Cech.DerivedComparison K.toPresheafTarget

/-- Lemma 25.5.3 (01GY), derived comparison clause: a fixed-target hypercovering admits a
Cech-to-derived-cohomology comparison natural in the coefficient sheaf. -/
@[stacks 01GY "existence of the derived comparison"]
theorem derivedComparison_nonempty (K : Hypercovering.{w} J X) :
    Nonempty (DerivedComparison K) := sorry

namespace DerivedComparison

/-- Applying degree-`n` homology to a derived comparison gives a natural transformation of
coefficient functors. -/
@[stacks 01GY "degree comparison"]
noncomputable def homology {K : Hypercovering.{w} J X}
    (α : CategoryTheory.Hypercovering.Cech.DerivedComparison (J := J) K) (n : ℤ) :
    derivedSource K ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n ⟶
      derivedTarget (J := J) (X := X) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n :=
  HypercoveringOf.Cech.DerivedComparison.homology α n

end DerivedComparison

/-- In nonnegative degree, homology of the derived Cech source recovers ordinary fixed-target
Cech cohomology, naturally in the coefficient sheaf. -/
@[stacks 01GY "derived source cohomology"]
theorem derivedSource_homology_isIsomorphic
    (K : Hypercovering.{w} J X) (n : ℕ) :
    IsIsomorphic
      (derivedSource K ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n)
      (cohomologyInCoefficients K n) := sorry

/-- In nonnegative degree, homology of the fixed-target derived target recovers objectwise
sheaf cohomology, naturally in the coefficient sheaf. -/
@[stacks 01GY "derived target cohomology"]
theorem derivedTarget_homology_isIsomorphic
    [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
    (n : ℕ) :
    IsIsomorphic
      (derivedTarget (J := J) (X := X) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n)
      (Sheaf.cohomologyOverObjectFunctor J X n) := sorry

end CategoryTheory.Hypercovering.Cech
