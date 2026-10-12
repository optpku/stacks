/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import stacks_project.Chap109.Lemma_109_21_3
public import stacks_project.Chap109.Lemma_109_21_4_Substack

/-!
# Semistable curves of a given genus

There is a decomposition of `𝒞urves^{semistable}` into open-and-closed
substacks `𝒞urves^{semistable}_g` for `g ≥ 1`, classifying semistable
families of curves for which `R¹ f_* 𝒪_X` is locally free of rank `g`,
equivalently proper schemes of dimension `1` over a field with at-worst-nodal
singularities, `H⁰(X, 𝒪_X) = k`, genus `g`, and either no rational tail or
`ω_X^{⊗ m}` globally generated for all `m ≥ 2`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.21.4 (1): the semistable locus `𝒞urves^{semistable}` decomposes as
the coproduct of open-and-closed substacks `𝒞urves^{semistable}_g` for
`g ≥ 1`. -/
@[stacks 0E71]
theorem semistable_eq_iSup_semistableOfGenus (S : Scheme.{u}) :
    semistable S = ⨆ g : ℕ, semistableOfGenus (g + 1) S :=
  sorry

/-- Lemma 109.21.4 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{semistable}_g` if and only if
`X ⟶ S` is a semistable family of curves and `R¹ f_* 𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. -/
@[stacks 0E71]
theorem classifying_factorsThrough_semistableOfGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    semistableOfGenus g S P ↔
      AlgebraicSpace.Semistable (hom P) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.21.4 (3): given a scheme `X` proper over a field `k` with
dimension at most one and `g ≥ 1`, the classifying morphism
`Spec k ⟶ 𝒞urves` factors through `𝒞urves^{semistable}_g` if and only if
the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
`k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`, and `X` has no rational tails. -/
@[stacks 0E71]
theorem classifying_factorsThrough_semistableOfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 1 ≤ g) :
    semistableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            ¬ Nonempty (SchemeOverField.RationalTail X) :=
  sorry

/-- Lemma 109.21.4 (4): given a scheme `X` proper over a field `k` with
dimension at most one and `g ≥ 1`, the classifying morphism
`Spec k ⟶ 𝒞urves` factors through `𝒞urves^{semistable}_g` if and only if
the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
`k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`, and `ω_X^{⊗ m}` is globally
generated for all `m ≥ 2`. -/
@[stacks 0E71]
theorem classifying_factorsThrough_semistableOfGenus_iff_scheme_dualizing
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 1 ≤ g) :
    semistableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            dualizingTensorPowersGloballyGenerated X :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
