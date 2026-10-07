module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Lemma_87_10_3_Types
public import stacks_project.Chap87.Lemma_87_10_4_Predicates

/-!
# Lemma 87.10.4

Characterizations of countably indexed affine formal algebraic spaces as
`Spf` of sequential presentations of topological `S`-algebras.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.AffineFormalAlgebraicSpace
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsAffineFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsAffineFormalAlgebraicSpace

/-- Lemma 87.10.4: Let `S` be a scheme. Let `X` be a presheaf on
`(Sch/S)_fppf`. The following are equivalent: `X` is a countably indexed
affine formal algebraic space; `X ≅ Spf(A)` for a weakly admissible
topological `S`-algebra `A` with a countable fundamental system of
neighbourhoods of `0`; `X ≅ Spf(A)` for a weakly admissible topological
`S`-algebra `A` with a nested countable fundamental system
`A ⊇ I 1 ⊇ I 2 ⊇ I 3 ⊇ …` of weak ideals of definition; `X ≅ Spf(A)` for a
complete topological `S`-algebra `A` with a nested countable fundamental
system of open neighbourhoods of `0` given by ideals `I n` such that
`I n / I (n + 1)` is locally nilpotent; and `X ≅ Spf(A)` where
`A = lim B ⧸ J n` with the limit topology for a nested sequence of ideals
in an `S`-algebra `B` with `J n / J (n + 1)` locally nilpotent. -/
@[stacks 0AN1]
theorem tfae_spf {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    List.TFAE [IsCountablyIndexedAffine X, isColimitOfCountablyGeneratedSpf X,
      isColimitOfWeakIdealSequence X,
      isColimitOfCompleteLocallyNilpotentSequence X,
      isColimitOfQuotientInverseLimit X] :=
  sorry

/-- Countably indexed affine formal algebraic spaces are exactly `Spf` of a
weakly admissible topological `S`-algebra with countably generated
neighbourhoods of `0`. -/
theorem isCountablyIndexedAffine_iff_isColimitOfCountablyGeneratedSpf
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsCountablyIndexedAffine X ↔ isColimitOfCountablyGeneratedSpf X :=
  sorry

/-- A weakly admissible countable neighbourhood presentation is equivalent to
a nested countable fundamental system of weak ideals of definition. -/
theorem isColimitOfCountablyGeneratedSpf_iff_isColimitOfWeakIdealSequence
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfCountablyGeneratedSpf X ↔ isColimitOfWeakIdealSequence X :=
  sorry

/-- A complete locally nilpotent nested open-ideal presentation is a special
case of a quotient inverse-limit presentation, by taking `B = A`. -/
theorem isColimitOfQuotientInverseLimit_of_isColimitOfCompleteLocallyNilpotentSequence
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfCompleteLocallyNilpotentSequence X →
      isColimitOfQuotientInverseLimit X :=
  sorry

/-- A quotient inverse-limit presentation yields a weakly admissible
`S`-algebra with countably generated neighbourhoods of `0`. -/
theorem isColimitOfCountablyGeneratedSpf_of_isColimitOfQuotientInverseLimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    isColimitOfQuotientInverseLimit X → isColimitOfCountablyGeneratedSpf X :=
  sorry

end AlgebraicGeometry.IsAffineFormalAlgebraicSpace
