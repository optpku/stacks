/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Lemma_109_9_4_Substack

/-!
# Curves of a given genus

There is a decomposition of `𝒞urves^{h0, 1}` into open-and-closed substacks
`𝒞urves_g` for `g ≥ 0`, classifying families of curves for which
`𝒪_S ⟶ f_* 𝒪_X` is an isomorphism after every base change, every fibre has
dimension `1`, and `R^1 f_* 𝒪_X` is locally free of rank `g`, equivalently
proper schemes of dimension `1` over a field with `H^0(X, 𝒪_X) = k` and
genus `g`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.9.4 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves_g` if and only if `𝒪_S ⟶ f_* 𝒪_X`
is an isomorphism after every base change (including the identity), the fibres
of `X ⟶ S` have dimension `1`, and `R^1 f_* 𝒪_X` is a locally free `𝒪_S`-module
of rank `g`. -/
@[stacks 0E6K]
theorem classifying_factorsThrough_ofGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    ofGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        (∀ y : Points (ofOver (base P)), fiberDimension (hom P) y = 1) ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.9.4 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves_g` if and only if `dim(X) = 1`, `k = H^0(X, 𝒪_X)`, and the
genus of `X` is `g`. -/
@[stacks 0E6K]
theorem classifying_factorsThrough_ofGenus_iff_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    ofGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      ∃ (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
        SchemeOverField.genus X hdim1 hΓ = g :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
