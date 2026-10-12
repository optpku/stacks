/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap109.Lemma_109_16_3_Substack

/-!
# Smooth curves with universally trivial pushforward of 𝒪

There is an open substack `𝒞urves^{smooth, h0} ⊂ 𝒞urves` classifying smooth
families of curves with universally trivial `𝒪_S ⟶ f_* 𝒪_X`, equivalently
proper smooth schemes of dimension one over a field with `k = H⁰(X, 𝒪_X)`,
equivalently geometrically connected, equivalently geometrically integral,
equivalently becoming a smooth curve after base change to an algebraic
closure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.16.3 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{smooth, h0}` if and only if
`𝒪_S ⟶ f_* 𝒪_X` is an isomorphism after every base change (including the
identity) and `X ⟶ S` is smooth of relative dimension `1`. -/
@[stacks 0E81]
theorem classifying_factorsThrough_smoothH0_iff
    {S : Scheme.{u}} (P : Obj S) :
    smoothH0 S P ↔
      (∀ {Z : AlgebraicSpace S} (g : Z ⟶ ofOver (base P)),
          IsIso (Modules.unitToPushforwardObjUnit (pullback.snd (hom P) g))) ∧
        AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1 :=
  sorry

/-- Lemma 109.16.3 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{smooth, h0}` if and only if `X` is smooth of dimension `1`
with `k = H⁰(X, 𝒪_X)`, if and only if `X` is smooth of dimension `1` and
geometrically connected, if and only if `X` is smooth of dimension `1` and
geometrically integral, if and only if `X` base-changed to an algebraic
closure of `k` is a smooth curve. -/
@[stacks 0E81]
theorem classifying_factorsThrough_smoothH0_tfae_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    List.TFAE
      [smoothH0 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          Function.Bijective (Scheme.Hom.globalSectionsMap X.hom),
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          GeometricallyConnected X.hom,
        AlgebraicGeometry.Smooth X.hom ∧ topologicalKrullDim X.left = 1 ∧
          GeometricallyIntegral X.hom,
        Curve (FieldExtension.Over.baseChange k (AlgebraicClosure k) X) ∧
          AlgebraicGeometry.Smooth (FieldExtension.Over.baseChange k (AlgebraicClosure k) X).hom] :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
