module

public import stacks_project.Chap87.Lemma_87_17_1

/-!
# Quasi-compact formal algebraic spaces

A formal algebraic space is quasi-compact when the equivalent conditions of
Lemma 87.17.1 hold.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- Definition 87.17.2: Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. We say `X` is quasi-compact if the equivalent conditions of
Lemma 87.17.1 are satisfied. -/
@[stacks 0AJA]
class IsQuasiCompact {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Prop where
  /-- The reduction of `X` (Lemma 87.12.1) is a quasi-compact algebraic space. -/
  isQuasiCompact_reduction : ChosenBigFppfSite.IsQuasiCompact (reduction X)

namespace IsQuasiCompact

/-- An affine formal algebraic space is quasi-compact. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsQuasiCompact X := sorry

/-- A formal algebraic space is quasi-compact if and only if each of the
equivalent conditions of Lemma 87.17.1 holds: the reduction is a
quasi-compact algebraic space, there is a finite étale affine atlas, and
there is an affine étale cover. -/
theorem tfae {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [IsQuasiCompact X, ChosenBigFppfSite.IsQuasiCompact (reduction X),
      HasFiniteAffineEtaleAtlas X, HasAffineEtaleCover X] := sorry

end IsQuasiCompact

end AlgebraicGeometry.IsFormalAlgebraicSpace
