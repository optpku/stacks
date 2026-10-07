module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_21_9_Spf

/-!
# Faithfully flat criteria for rig-surjectivity

If `A` is Noetherian and `I`-adically complete, `B` is an `I`-adically complete
`A`-algebra, and each truncation `A ⧸ I ^ n →+* B ⧸ I ^ n B` is of finite type
and flat, and faithfully flat for `n = 1`, then the induced morphism of formal
spectra `Spf(B) ⟶ Spf(A)` is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicSpace FormalAlgebraicSpace AffineFormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The completion of `Spec(A)` along `Spec(A ⧸ I)` is a formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlongIdeal {A : Type u}
    [CommRing A] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsFormalAlgebraicSpace (completionAlongSubspace (closedImmersion hA I)) :=
  sorry

/-- The completion of `Spec(A)` along `Spec(A ⧸ I)` is locally Noetherian when
`A` is Noetherian. -/
instance instIsLocallyNoetherian_completionAlongIdeal {A : Type u} [CommRing A]
    [IsNoetherianRing A] {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) (I : Ideal A) :
    IsLocallyNoetherian (completionAlongSubspace (closedImmersion hA I)) :=
  sorry

/-- Completeness together with finite type of the special fiber
`A ⧸ I → B ⧸ IB` makes the completion of `Spec(B)` along `V(IB)` locally
Noetherian. -/
instance instIsLocallyNoetherian_completionAlongIdeal_algebra
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    IsLocallyNoetherian
      (completionAlongSubspace
        (closedImmersion
          (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ hA)
          (I.map (algebraMap A B)))) :=
  sorry

/-- The morphism of sheafy formal spectra induced by an `I`-adically complete
algebra over a Noetherian ring is locally of finite type, given finite type of
the special fiber. -/
instance locallyOfFiniteType_spfAdicCompletionMap
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    LocallyOfFiniteType (spfAdicCompletionMap B hA I) :=
  sorry

namespace RigSurjective

/-- Lemma 88.21.9: Let `A` be a Noetherian ring complete with respect to an
ideal `I`. Let `B` be an `I`-adically complete `A`-algebra. If
`A ⧸ I ^ n →+* B ⧸ I ^ n B` is of finite type and flat for all `n` and
faithfully flat for `n = 1`, then `Spf(B) ⟶ Spf(A)` is rig-surjective. -/
@[stacks 0AQX]
theorem of_finiteType_flat
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [Algebra A B]
    (I : Ideal A) [IsAdicComplete I A] [IsAdicComplete I B]
    [Algebra.FiniteType (A ⧸ I) (B ⧸ I.map (algebraMap A B))]
    (hfinite : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FiniteType)
    (hflat : ∀ n : ℕ,
      (Ideal.quotientMap ((I ^ (n + 1)).map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).Flat)
    (hff :
      (Ideal.quotientMap (I.map (algebraMap A B))
        (algebraMap A B) Ideal.le_comap_map).FaithfullyFlat)
    {S : Scheme.{u}} (hA : Spec (.of A) ⟶ S) :
    RigSurjective (spfAdicCompletionMap B hA I) :=
  sorry

end RigSurjective

end AlgebraicGeometry.FormalAlgebraicSpace
