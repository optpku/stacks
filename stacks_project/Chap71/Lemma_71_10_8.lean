module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import stacks_project.Chap67.Definition_67_47_3_RationalFunction
public import stacks_project.Chap71.Definition_71_10_1_MeromorphicFunction
public import stacks_project.Chap71.Definition_71_10_3_MeromorphicSection
public import stacks_project.Chap71.Lemma_71_10_8_Stalk
public import stacks_project.Chap71.Lemma_71_10_8_Pushforward

/-!
# Lemma 71.10.8

If every weakly associated point of an algebraic space `X` has codimension `0`, `X` satisfies
Morphisms of Spaces Lemma 67.49.1, and every codimension-`0` point is represented by a
monomorphism `Spec(k) ⟶ X`, then `𝒦_X` is the product of `j_{η,*} 𝒪_{X,η}` over `η ∈ X^0`,
the same formula holds for meromorphic sections of a quasi-coherent module, and
`R(X) = Γ(X, 𝒦_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.10.8 (1): if every weakly associated point of `X` has codimension `0`, `X`
satisfies Morphisms of Spaces Lemma 67.49.1, and every codimension-`0` point is represented
by a monomorphism `Spec(k) ⟶ X`, then `𝒦_X` is isomorphic to `∏_{η ∈ X^0} j_{η,*} 𝒪_{X,η}`. -/
@[stacks 0ENA]
theorem meromorphicFunctionSheaf_iso_codimZeroStalkPushforwardProduct
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    IsIsomorphic (meromorphicFunctionSheaf X)
      (codimZeroStalkPushforwardProductSheaf hweak hmono) :=
  sorry

/-- Lemma 71.10.8 (2): under the same hypotheses, if `ℱ` is a quasi-coherent `𝒪_X`-module,
then `𝒦_X(ℱ)` is isomorphic to `∏_{η ∈ X^0} j_{η,*} ℱ_η` after restriction of scalars along
`𝒪_X ⟶ 𝒦_X`. -/
@[stacks 0ENA]
theorem meromorphicSectionSheaf_iso_codimZeroStalkPushforwardProduct
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (F : X.Modules) [F.IsQuasicoherent] :
    IsIsomorphic
      ((restrictionAlong (toMeromorphicFunctionSheafHom X)).obj
        (meromorphicSectionSheaf X F))
      (codimZeroStalkPushforwardProductModule hweak hmono F) :=
  sorry

/-- Lemma 71.10.8 (3): under the same hypotheses, the ring of rational functions of `X` is
isomorphic to the ring of global meromorphic functions `Γ(X, 𝒦_X)`. -/
@[stacks 0ENA]
theorem rationalFunctionRing_iso_meromorphicFunctions {S : Scheme.{u}}
    (X : AlgebraicSpace S) [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η) :
    IsIsomorphic (rationalFunctionRing X) (meromorphicFunctions X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
