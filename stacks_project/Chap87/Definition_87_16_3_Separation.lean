module

public import stacks_project.Chap87.Lemma_87_16_1
public import stacks_project.Chap87.Lemma_87_16_2

/-!
# Quasi-separated and separated formal algebraic spaces

A formal algebraic space is quasi-separated or separated when the equivalent
conditions of Lemma 87.16.1 or Lemma 87.16.2 hold.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- A formal algebraic space is quasi-separated when its reduction is a
quasi-separated algebraic space. -/
class IsQuasiSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Prop where
  /-- The reduction of `X` (Lemma 87.12.1) is a quasi-separated algebraic
  space. -/
  isQuasiSeparated_reduction : ChosenBigFppfSite.IsQuasiSeparated (reduction X)

/-- A formal algebraic space is separated when its reduction is a separated
algebraic space. -/
class IsSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Prop where
  /-- The reduction of `X` (Lemma 87.12.1) is a separated algebraic space. -/
  isSeparated_reduction : ChosenBigFppfSite.IsSeparated (reduction X)

namespace IsQuasiSeparated

/-- An affine formal algebraic space is quasi-separated. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsQuasiSeparated X := sorry

/-- A separated formal algebraic space is quasi-separated. -/
instance (priority := 900) of_separated {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] [IsSeparated X] : IsQuasiSeparated X :=
  sorry

/-- A formal algebraic space is quasi-separated if and only if each of the
equivalent conditions of Lemma 87.16.1 holds: the reduction is a
quasi-separated algebraic space, fibre products of morphisms from
quasi-compact schemes are quasi-compact, and the same with affine schemes. -/
theorem tfae {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [IsQuasiSeparated X, ChosenBigFppfSite.IsQuasiSeparated (reduction X),
      ChosenBigFppfSite.forallQuasiCompactPullback X,
      ChosenBigFppfSite.forallAffineQuasiCompactPullback X] := sorry

/-- A formal algebraic space is quasi-separated if and only if its reduction is
a quasi-separated algebraic space. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    IsQuasiSeparated X ↔ ChosenBigFppfSite.IsQuasiSeparated (reduction X) :=
  sorry

/-- The reduction of a quasi-separated formal algebraic space is a
quasi-separated algebraic space. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] [IsQuasiSeparated X] :
    ChosenBigFppfSite.IsQuasiSeparated (reduction X) := sorry

/-- A formal algebraic space whose reduction is a quasi-separated algebraic
space is quasi-separated. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsFormalAlgebraicSpace X]
    (h : ChosenBigFppfSite.IsQuasiSeparated (reduction X)) :
    IsQuasiSeparated X := sorry

end IsQuasiSeparated

namespace IsSeparated

/-- An affine formal algebraic space is separated. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsSeparated X := sorry

/-- A formal algebraic space is separated if and only if each of the
equivalent conditions of Lemma 87.16.2 holds: the reduction is a separated
algebraic space, and fibre products of morphisms from affine schemes are
affine with surjective `sectionTensor`. -/
theorem tfae {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [IsSeparated X, ChosenBigFppfSite.IsSeparated (reduction X),
      ChosenBigFppfSite.forallAffinePullbackAffineSurjective X] := sorry

/-- A formal algebraic space is separated if and only if its reduction is a
separated algebraic space. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    IsSeparated X ↔ ChosenBigFppfSite.IsSeparated (reduction X) := sorry

/-- The reduction of a separated formal algebraic space is a separated
algebraic space. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] [IsSeparated X] :
    ChosenBigFppfSite.IsSeparated (reduction X) := sorry

/-- A formal algebraic space whose reduction is a separated algebraic space is
separated. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsFormalAlgebraicSpace X]
    (h : ChosenBigFppfSite.IsSeparated (reduction X)) : IsSeparated X :=
  sorry

end IsSeparated

end AlgebraicGeometry.IsFormalAlgebraicSpace
