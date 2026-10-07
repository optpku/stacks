module

public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.HomComplex.KInjective
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable (K : CochainComplex (Modules X) ℤ) [K.IsKInjective]
variable (n : ℤ)

/- 75.17.3.1: since K is K-injective, H^n(E) = Ext^n_{D(𝒪_X)}(K, K)
for all n : ℤ, where E = Hom_Comp^{dg}(𝒪_X)(K, K). This is the canonical
linear equivalence from homology of `homComplex K K` to
`ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj K) n`. -/
@[stacks 09MD] #check
  (CategoryTheory.CochainComplex.Enriched.injectiveDerivedHomLinearEquiv K K K (𝟙 K) n :
    (DifferentialGradedCategory.homComplex K K).homology n ≃ₗ[ℤ]
      ShiftedHom (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj K) n)
