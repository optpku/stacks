/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleCompletion.Surjective
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.FaithfullyFlat
import StacksCheckRecall

/-!
# Surjectivity of étale Spf maps versus faithful flatness

In the setup of Lemma 87.19.13, the morphism `Spf((A)^∧) ⟶ Spf(B)`
associated to an étale `B`-algebra `A` is surjective if and only if
`B → A` is faithfully flat, equivalently if and only if this holds after
quotienting by a weak ideal of definition of `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
  (A : Type u) [CommRing A] [Algebra B A] [Algebra.Etale B A]

/- Lemma 87.19.14: With notation and assumptions as in Lemma 87.19.13, let
`f : X ⟶ Y` correspond to `B → (A)^∧`, where `Y = Spf(B)` and
`X = Spf((A)^∧)` for an étale `B`-algebra `A`. The following are equivalent:
`f` is surjective, `B → A` is faithfully flat, for every weak ideal of
definition `J ⊂ B` the map `B ⧸ J → A ⧸ J A` is faithfully flat, and for some
such `J` the map `B ⧸ J → A ⧸ J A` is faithfully flat. -/
@[stacks 0AN9] #check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_weakIdealCompletion_surjective_tfae
    hB A :
    let f := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
      (spfMap_weakIdealCompletion hB A)
    List.TFAE
      [AlgebraicSpace.representableByAlgebraicSpaces f ∧
        ∀ (ha : AlgebraicSpace.representableByAlgebraicSpaces f) ⦃U : Over S⦄
          (ξ : yoneda.obj U ⟶
            (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB)),
          AlgebraicSpace.Surjective (ha.pullbackHom ξ),
        (algebraMap B A).FaithfullyFlat,
        ∀ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J →
          (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat,
        ∃ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J ∧
          (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat])

/- `Spf((A)^∧) ⟶ Spf(B)` is surjective on scheme Yoneda pullbacks if and only if
`algebraMap B A` is faithfully flat. -/
#check
  (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_weakIdealCompletion_surjective_iff_faithfullyFlat
    hB A :
    let f := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
      (spfMap_weakIdealCompletion hB A)
    (AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ (ha : AlgebraicSpace.representableByAlgebraicSpaces f) ⦃U : Over S⦄
        (ξ : yoneda.obj U ⟶
          (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB)),
        AlgebraicSpace.Surjective (ha.pullbackHom ξ)) ↔
      (algebraMap B A).FaithfullyFlat)

/- `algebraMap B A` is faithfully flat if and only if
`algebraMap (B ⧸ J) (A ⧸ J A)` is faithfully flat for every weak ideal of
definition `J ⊂ B`. -/
#check (TopologicalRing.algebraMap_faithfullyFlat_iff_forall_weakIdeal_quotient B A :
    (algebraMap B A).FaithfullyFlat ↔
      ∀ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J →
        (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat)

/- `algebraMap B A` is faithfully flat if and only if
`algebraMap (B ⧸ J) (A ⧸ J A)` is faithfully flat for some weak ideal of
definition `J ⊂ B`. -/
#check (TopologicalRing.algebraMap_faithfullyFlat_iff_exists_weakIdeal_quotient B A :
    (algebraMap B A).FaithfullyFlat ↔
      ∃ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J ∧
        (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat)

end AlgebraicGeometry.AffineFormalAlgebraicSpace
