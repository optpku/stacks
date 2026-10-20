/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced
public import stacks_project.Chap109.Lemma_109_7_3_Aut
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_8_1_Substack

/-!
# Curves with finite reduced automorphism groups

There is a maximal open DM substack `𝒞urves^{DM} ⊂ 𝒞urves`. A family of curves
is classified by this substack if and only if its automorphism algebraic space
is unramified over the base, and for a proper scheme of dimension at most one
over a field this is equivalent to the automorphism space being geometrically
reduced of dimension `0`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- Lemma 109.7.3 (1): `𝒞urves^{DM} ⊂ 𝒞urves` is the maximal open substack which
is DM: every open DM substack of families of curves is contained in `dm`. -/
@[stacks 0DSW]
theorem dm_isLargest {S : Scheme.{u}} (Q : ObjectProperty (Obj S))
    [IsOpenDMSubstack Q] : Q ≤ dm S :=
  sorry

/-- Lemma 109.7.3 (2): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{DM}` if and only if the group
algebraic space `Aut_S(X)` is unramified over `S`. -/
@[stacks 0DSW]
theorem classifying_factorsThrough_dm_iff {S : Scheme.{u}} (P : Obj S) :
    dm S P ↔ IsUnramified P :=
  sorry

/-- Lemma 109.7.3 (3): given a proper scheme `X` over a field `k` of dimension
at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors through
`𝒞urves^{DM}` if and only if `Aut(X)` is geometrically reduced over `k` and has
dimension `0`, if and only if `Aut(X) ⟶ Spec k` is unramified. -/
@[stacks 0DSW]
theorem classifying_factorsThrough_dm_tfae_scheme
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    List.TFAE
      [dm (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim),
        (∀ G : AlgebraicSpace (Spec (CommRingCat.of k)),
          IsRepresentedBy (mkOfSchemeOverField X hdim) G →
            GeometricallyReduced G ∧ dimension G = 0),
        IsUnramified (mkOfSchemeOverField X hdim)] :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
