/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Clopen
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over.Proper
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import stacks_project.Chap109.Lemma_109_11_3_Substack
public import stacks_project.Chap109.Lemma_109_16_5_Substack

/-!
# Smooth curves of a given genus

There is a decomposition of `𝒞urves^{smooth, h0}` into open-and-closed
substacks `𝒞urves^{smooth, h0}_g` for `g ≥ 0`, witnessed on families by a
pairwise-disjoint clopen cover of the base, classifying smooth families
of curves with universally trivial `𝒪_S ⟶ f_* 𝒪_X` for which
`R¹ f_* 𝒪_X` is locally free of rank `g`, equivalently proper smooth
schemes of dimension one over a field with `k = H⁰(X, 𝒪_X)` and genus `g`,
equivalently geometrically connected, equivalently geometrically integral,
equivalently becoming a smooth curve of genus `g` after base change to an
algebraic closure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.16.5 (1): the moduli stack `ℳ = 𝒞urves^{smooth, h0}`
decomposes as the coproduct of open-and-closed substacks `ℳ_g` for
`g ≥ 0`: a family lies in `ℳ` if and only if its base admits a
pairwise-disjoint clopen cover `(U_g)_{g : ℕ}`, with pieces possibly
empty, such that the base change to each `U_g` lies in `ℳ_g`. -/
@[stacks 0E83]
theorem smoothH0_iff_clopenCover {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P ↔
      ∃ U : ℕ → (base P).left.Opens,
        iSup U = ⊤ ∧
          Pairwise (fun g g' ↦
              Disjoint (U g : Set (base P).left) (U g')) ∧
            (∀ g, IsClopen (U g : Set (base P).left)) ∧
              ∀ g, smoothH0OfGenus g S (baseChangeToOpen P (U g)) :=
  sorry

/-- Lemma 109.16.5 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `ℳ_g` if and only if `𝒪_S ⟶ f_* 𝒪_X`
is an isomorphism after every base change (including the identity),
`X ⟶ S` is smooth of relative dimension `1`, and `R¹ f_* 𝒪_X` is a locally
free `𝒪_S`-module of rank `g`. -/
@[stacks 0E83]
theorem classifying_factorsThrough_smoothH0OfGenus_iff
    {S : Scheme.{u}} (P : Obj S) (g : ℕ) :
    smoothH0OfGenus g S P ↔
      (∀ {Z : AlgebraicSpace S} (φ : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) φ))) ∧
        AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 ∧
          SheafOfModules.IsFiniteLocallyFreeOfRank g
            (higherDirectImageOne (hom P)) :=
  sorry

/-- Lemma 109.16.5 (3): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `ℳ_g` if and only if `X` is smooth of dimension `1` with
`k = H⁰(X, 𝒪_X)` and genus `g`, if and only if `X` is smooth of dimension
`1`, geometrically connected, and of genus `g`, if and only if `X` is
smooth of dimension `1`, geometrically integral, and of genus `g`, if and
only if `X` base-changed to an algebraic closure of `k` is a smooth curve
of genus `g`. -/
@[stacks 0E83]
theorem classifying_factorsThrough_smoothH0OfGenus_tfae_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) :
    List.TFAE
      [smoothH0OfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        AlgebraicGeometry.Smooth X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g,
        AlgebraicGeometry.Smooth X.hom ∧ GeometricallyConnected X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g,
        AlgebraicGeometry.Smooth X.hom ∧ GeometricallyIntegral X.hom ∧
          ∃ (hdim1 : topologicalKrullDim X.left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
            SchemeOverField.genus X hdim1 hΓ = g,
        Curve (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) ∧
          AlgebraicGeometry.Smooth
            (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom ∧
          ∃ (hdim1 : topologicalKrullDim
                (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).left = 1)
            (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap
                (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom)),
            SchemeOverField.genus
              (FieldExtension.Over.baseChange k (AlgebraicClosure k) X)
              hdim1 hΓ = g] :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
