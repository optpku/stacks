/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import stacks_project.Chap109.Lemma_109_7_3

/-!
# Curves with finite reduced automorphism groups

For a proper scheme of dimension at most one over a field, the equivalent
conditions of Lemma 109.7.3 (3) are also equivalent to vanishing of global
`k`-derivations of `𝒪_X` into itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.7.4: given a proper scheme `X` over a field `k` of dimension at
most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors through
`𝒞urves^{DM}` if and only if `Aut(X)` is geometrically reduced over `k` and has
dimension `0`, if and only if `Aut(X) ⟶ Spec k` is unramified, if and only if
`Der_k(𝒪_X, 𝒪_X) = 0`. -/
@[stacks 0E6G]
theorem classifying_factorsThrough_dm_tfae_scheme_derivations
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    List.TFAE
      [dm (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        (∀ G : AlgebraicSpace (Spec (CommRingCat.of k)),
          IsRepresentedBy (mkOfSchemeOverField X hdim) G →
            GeometricallyReduced G ∧ dimension G = 0),
        IsUnramified (mkOfSchemeOverField X hdim),
        Subsingleton
          (RingedSpace.Hom.derivations X.hom.toShHom
            (SheafOfModules.unit X.left.toRingedSpace.ringCatSheaf))] :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
