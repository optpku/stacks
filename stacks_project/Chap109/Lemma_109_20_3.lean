/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Lemma_109_20_3_Substack

/-!
# Prestable curves of a given genus

There is a decomposition of `𝒞urves^{prestable}` into open-and-closed
substacks `𝒞urves^{prestable}_g` for `g ≥ 0`, classifying prestable
families of curves for which `R¹ f_* 𝒪_X` is locally free of rank `g`,
equivalently proper schemes of dimension `1` over a field with at-worst-nodal
singularities, `H⁰(X, 𝒪_X) = k`, and genus `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.20.3 (1): the prestable locus `𝒞urves^{prestable}` decomposes as the
coproduct of open-and-closed substacks `𝒞urves^{prestable}_g` for `g ≥ 0`. -/
@[stacks 0E6V]
theorem prestable_eq_iSup_prestableOfGenus (S : Scheme.{u}) :
    prestable S = ⨆ g : ℕ, prestableOfGenus g S :=
  sorry

/-- Lemma 109.20.3 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{prestable}_g` if and only if
`X ⟶ S` is a prestable family of curves and `R¹ f_* 𝒪_X` is a locally free
`𝒪_S`-module of rank `g`. -/
@[stacks 0E6V]
theorem classifying_factorsThrough_prestableOfGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    prestableOfGenus g S P ↔
      Prestable (hom P) ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.20.3 (3): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{prestable}_g` if and only if the singularities of `X` are
at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, and the genus of `X` is `g`. -/
@[stacks 0E6V]
theorem classifying_factorsThrough_prestableOfGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    prestableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
