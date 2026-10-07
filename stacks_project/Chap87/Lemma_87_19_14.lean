module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_19_13_Functor

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

/-- Lemma 87.19.14: With notation and assumptions as in Lemma 87.19.13, let
`f : X ⟶ Y` correspond to `B → (A)^∧`, where `Y = Spf(B)` and
`X = Spf((A)^∧)` for an étale `B`-algebra `A`. The following are equivalent:
`f` is surjective, `B → A` is faithfully flat, for every weak ideal of
definition `J ⊂ B` the map `B ⧸ J → A ⧸ J A` is faithfully flat, and for some
such `J` the map `B ⧸ J → A ⧸ J A` is faithfully flat. -/
@[stacks 0AN9]
theorem spfMap_weakIdealCompletion_surjective_tfae :
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
          (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat] :=
  sorry

/-- `Spf((A)^∧) ⟶ Spf(B)` is surjective on scheme Yoneda pullbacks if and only if
`algebraMap B A` is faithfully flat. -/
theorem spfMap_weakIdealCompletion_surjective_iff_faithfullyFlat :
    let f := (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
      (spfMap_weakIdealCompletion hB A)
    (AlgebraicSpace.representableByAlgebraicSpaces f ∧
      ∀ (ha : AlgebraicSpace.representableByAlgebraicSpaces f) ⦃U : Over S⦄
        (ξ : yoneda.obj U ⟶
          (sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).obj (spf B hB)),
        AlgebraicSpace.Surjective (ha.pullbackHom ξ)) ↔
      (algebraMap B A).FaithfullyFlat :=
  sorry

/-- `algebraMap B A` is faithfully flat if and only if
`algebraMap (B ⧸ J) (A ⧸ J A)` is faithfully flat for every weak ideal of
definition `J ⊂ B`. -/
theorem algebraMap_faithfullyFlat_iff_forall_weakIdeal_quotient :
    (algebraMap B A).FaithfullyFlat ↔
      ∀ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J →
        (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat :=
  sorry

/-- `algebraMap B A` is faithfully flat if and only if
`algebraMap (B ⧸ J) (A ⧸ J A)` is faithfully flat for some weak ideal of
definition `J ⊂ B`. -/
theorem algebraMap_faithfullyFlat_iff_exists_weakIdeal_quotient :
    (algebraMap B A).FaithfullyFlat ↔
      ∃ (J : Ideal B), Ideal.IsWeakIdealOfDefinition J ∧
        (algebraMap (B ⧸ J) (A ⧸ J.map (algebraMap B A))).FaithfullyFlat :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
