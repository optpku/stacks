module

public import ReasLib.Algebra.PolynomialSite.LowerShriek
import StacksCheckRecall

/-!
# Underived lower shriek on a polynomial algebra

Lemma 92.4.6 records that if `B` is a polynomial `A`-algebra, then the underived
lower shriek `π_!` of `π` from 92.4.0.1 is exact and evaluates a presheaf at the
identity object `B ⟶ B`. The source proof applies Lemma 92.4.1 to the constant
simplicial algebra on `B`; equivalently, `B ⟶ B` is terminal in `PolynomialOver`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
universe u v w

/- Lemma 92.4.6. For a polynomial `A`-algebra `B`, underived lower shriek is exact. -/
@[stacks 08QG] #check (Algebra.PolynomialSite.lowerShriek_exact :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsPolynomial A B]
    (𝒜 : Type v) [Category.{w} 𝒜] [Abelian 𝒜]
    [HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ 𝒜],
    exactFunctor ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ 𝒜) 𝒜
      (colim : ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ 𝒜) ⥤ 𝒜))

#check (Algebra.PolynomialSite.lowerShriekIsoEval :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsPolynomial A B]
    (𝒜 : Type v) [Category.{w} 𝒜]
    [HasColimitsOfShape (Algebra.PolynomialSite A B)ᵒᵖ 𝒜],
    (colim : ((Algebra.PolynomialSite A B)ᵒᵖ ⥤ 𝒜) ⥤ 𝒜) ≅
      (evaluation ((Algebra.PolynomialSite A B)ᵒᵖ) 𝒜).obj
        (Algebra.PolynomialSite.evalObj A B))
