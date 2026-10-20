module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.CategoryTheory.Sites.Cohomology.Presheaf.Derived
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Cech.Refinement

/-!
# Derived comparison for presheaf-target hypercoverings

This leaf places the product-sections Cech complex and derived cohomology over the target
presheaf in the same bounded-below derived category.  The primary comparison is consequently a
single natural transformation of `D⁺`-valued coefficient functors; degreewise comparisons are
obtained by applying the homology functor.
-/

@[expose] public section

noncomputable section

universe d w v u

namespace CategoryTheory.HypercoveringOf.Cech

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{max w v})]
variable [HasDerivedCategory.{d} AddCommGrpCat.{max u v w}]
variable {G : Cᵒᵖ ⥤ Type (max w v)}
variable
  [(Sheaf.CohomologyOverPresheaf.homFunctor J G).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]

/-- The Cech complex of `K`, extended by zero and localized in the bounded-below derived
category, functorially in the coefficient sheaf. -/
@[stacks 09VX "derived Cech source"]
abbrev derivedSource (K : HypercoveringOf.{w} J G) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  complexInCoefficients K ⋙
    CochainComplex.Plus.extendNat AddCommGrpCat.{max u v w} ⋙
    DerivedCategory.Plus.Q

/-- Derived cohomology over `G`, restricted to coefficient sheaves placed in degree zero. -/
@[stacks 09VX "derived presheaf-cohomology target"]
abbrev derivedTarget :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max u v w} :=
  Sheaf.CohomologyOverPresheaf.coefficientFunctor J G

/-- A coefficient-natural morphism in `D⁺` from the Cech complex of `K` to derived
cohomology over its target presheaf, subject to the degree-zero augmentation condition. -/
@[stacks 09VX "derived comparison datum"]
structure DerivedComparison (K : HypercoveringOf.{w} J G) where
  /-- The comparison natural in the coefficient sheaf. -/
  hom : derivedSource K ⟶ derivedTarget (J := J) (G := G)
  /-- The degree-zero homology comparison is invertible for every coefficient sheaf. -/
  homologyZero_isIso (I : Sheaf J AddCommGrpCat.{max w v}) :
    IsIso
      ((Functor.whiskerRight hom
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} 0)).app I)

/-- Lemma 25.6.4 (Tag 09VX), primary comparison clause: a presheaf-target hypercovering has a
coefficient-natural comparison morphism in the bounded-below derived category. -/
@[stacks 09VX "derived comparison"]
theorem derivedComparison_nonempty (K : HypercoveringOf.{w} J G) :
    Nonempty (DerivedComparison K) := sorry

namespace DerivedComparison

/-- Applying degree-`n` homology to a derived comparison gives a natural transformation of
coefficient functors. -/
noncomputable def homology {K : HypercoveringOf.{w} J G}
    (alpha : DerivedComparison K) (n : ℤ) :
    derivedSource K ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n ⟶
      derivedTarget (J := J) (G := G) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n :=
  Functor.whiskerRight alpha.hom
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n)

end DerivedComparison

/-- In nonnegative degree, homology of the derived Cech source recovers ordinary Cech
cohomology, naturally in the coefficient sheaf. -/
theorem derivedSource_homology_isIsomorphic
    (K : HypercoveringOf.{w} J G) (n : ℕ) :
    IsIsomorphic
      (derivedSource K ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n)
      (cohomologyInCoefficients K n) := sorry

/-- In nonnegative degree, homology of the derived target recovers cohomology over the target
presheaf, naturally in the coefficient sheaf. -/
@[stacks 09VX "derived target cohomology"]
theorem derivedTarget_homology_isIsomorphic
    [HasExt.{max u v w} (Sheaf J AddCommGrpCat.{max w v})]
    (n : ℕ) :
    IsIsomorphic
      (derivedTarget (J := J) (G := G) ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} n)
      (Sheaf.cohomologyOverPresheafFunctor J G n) := sorry

end CategoryTheory.HypercoveringOf.Cech
