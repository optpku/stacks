module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Lemma_109_22_5_Substack

/-!
# Stable curves of a given genus

There is a decomposition of `𝒞urves^{stable}` into open-and-closed
substacks `𝒞urves^{stable}_g` for `g ≥ 2`, classifying stable families
of curves for which `R¹ f_* 𝒪_X` is locally free of rank `g`, equivalently
proper schemes of dimension `1` over a field with at-worst-nodal
singularities, `H⁰(X, 𝒪_X) = k`, genus `g`, and either no rational tails
or bridges, or with `ω_X` ample.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.22.5 (1): the stable locus `𝒞urves^{stable}` decomposes as the
coproduct of open-and-closed substacks `𝒞urves^{stable}_g` for `g ≥ 2`. -/
@[stacks 0E78]
theorem stable_eq_iSup_stableOfGenus (S : Scheme.{u}) :
    stable S = ⨆ g : ℕ, stableOfGenus (g + 2) S :=
  sorry

/-- Lemma 109.22.5 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{stable}_g` if and only if
`X ⟶ S` is a stable family of curves and `R¹ f_* 𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. -/
@[stacks 0E78]
theorem classifying_factorsThrough_stableOfGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    stableOfGenus g S P ↔
      AlgebraicSpace.IsStableFamily (hom P) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.22.5 (3): given a scheme `X` proper over a field `k` with
dimension at most one and `g ≥ 2`, the classifying morphism
`Spec k ⟶ 𝒞urves` factors through `𝒞urves^{stable}_g` if and only if
the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
`k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`, and `X` has no rational tails
or bridges. -/
@[stacks 0E78]
theorem classifying_factorsThrough_stableOfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 2 ≤ g) :
    stableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            ¬ Nonempty (SchemeOverField.RationalTail X) ∧
            ¬ Nonempty (RationalBridge X) :=
  sorry

/-- Lemma 109.22.5 (4): given a scheme `X` proper over a field `k` with
dimension at most one and `g ≥ 2`, the classifying morphism
`Spec k ⟶ 𝒞urves` factors through `𝒞urves^{stable}_g` if and only if
the singularities of `X` are at-worst-nodal, `dim(X) = 1`,
`k = H⁰(X, 𝒪_X)`, the genus of `X` is `g`, and `ω_X` is ample. -/
@[stacks 0E78]
theorem classifying_factorsThrough_stableOfGenus_iff_scheme_dualizing
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 2 ≤ g) :
    stableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            Scheme.Modules.isAmpleObject (dualizingModule X.hom) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
