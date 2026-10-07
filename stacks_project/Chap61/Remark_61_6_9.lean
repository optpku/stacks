module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap61.Lemma_61_6_1
public import stacks_project.Chap61.Lemma_61_6_2
public import stacks_project.Chap61.Lemma_61_6_8
public import stacks_project.Chap61.Proposition_61_6_6
public import stacks_project.Chap61.Remark_61_6_9_IndZariskiLocalization

@[expose] public section

/-!
# Remark 61.6.9

Lemmas 61.6.1, 61.6.2, Proposition 61.6.6, and Lemma 61.6.8 remain true after
replacing ind-Zariski by the stronger Bhatt–Scholze stage
`RingHom.IndZariskiLocalization`. Stacks retains `RingHom.IndZariski` as the
working owner, as the analogue of `RingHom.IndEtale`.
-/

universe u v

open Algebra PrimeSpectrum

namespace RingHom.IndZariskiLocalization

/-- Remark 61.6.9 (1): Lemma 61.6.1 remains valid with ind-Zariski replaced by
ind-(Zariski localization). For a ring `A` and a closed subset `T` of
`ConnectedComponents (PrimeSpectrum A)`, there exists a surjective
ind-(Zariski localization) ring map `f : A →+* B` such that
`PrimeSpectrum.comap f` has range `ConnectedComponents.mk ⁻¹' T`. -/
@[stacks 0A0D]
theorem exists_surjective_of_isClosed_connectedComponents
    {A : Type u} [CommRing A] {T : Set (ConnectedComponents (PrimeSpectrum A))}
    (hT : IsClosed T) :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      Function.Surjective f ∧ f.IndZariskiLocalization ∧
        Set.range (comap f) = ConnectedComponents.mk ⁻¹' T :=
  sorry

/-- Remark 61.6.9 (2): Lemma 61.6.2 remains valid with ind-Zariski replaced by
ind-(Zariski localization). For a ring `A`, a profinite space `T`, and a
continuous map `φ : C(T, ConnectedComponents (PrimeSpectrum A))`, there exists
an ind-(Zariski localization) ring map `f : A →+* B` realizing `φ` by a
cartesian square and a homeomorphism of connected-components spaces. -/
@[stacks 0A0D]
theorem exists_pullback_of_continuousMap_connectedComponents
    {A : Type u} [CommRing A] {T : Type v}
    [TopologicalSpace T] [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]
    (φ : C(T, ConnectedComponents (PrimeSpectrum A))) :
    ∃ (B : Type (max u v)) (_ : CommRing B) (f : A →+* B)
      (p : C(PrimeSpectrum B, T))
      (hcomm : ∀ y, ConnectedComponents.mk (comap f y) = φ (p y)),
      f.IndZariskiLocalization ∧
        IsHomeomorph (ConnectedComponents.pullback.comparison hcomm) ∧
        IsHomeomorph p.continuous.connectedComponentsLift :=
  sorry

/-- Remark 61.6.9 (3): Proposition 61.6.6 remains valid with ind-Zariski
replaced by ind-(Zariski localization). If `f : A →+* B` identifies local
rings, then there exists a faithfully flat ind-(Zariski localization)
`g : B →+* B'` such that `g.comp f` is an ind-(Zariski localization). -/
@[stacks 0A0D]
theorem exists_faithfullyFlat_of_isIsoOnLocalRings
    {A B : Type u} [CommRing A] [CommRing B] {f : A →+* B}
    (hf : f.IsIsoOnLocalRings) :
    ∃ (B' : Type u) (_ : CommRing B') (g : B →+* B'),
      g.FaithfullyFlat ∧ g.IndZariskiLocalization ∧
        (g.comp f).IndZariskiLocalization :=
  sorry

/-- Remark 61.6.9 (4): Lemma 61.6.8 remains valid with ind-Zariski replaced by
ind-(Zariski localization). For a commutative ring `A`, there exists a
faithfully flat ind-(Zariski localization) `f : A →+* B` such that `B`
satisfies the equivalent conditions of Lemma 61.6.7. -/
@[stacks 0A0D]
theorem exists_faithfullyFlat_indZariskiRetraction (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      f.FaithfullyFlat ∧ f.IndZariskiLocalization ∧
        HasFaithfullyFlatIndZariskiRetraction B :=
  sorry

end RingHom.IndZariskiLocalization
