module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.SequentialSpf
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsAffineFormalAlgebraicSpace

universe u

/- Lemma 87.10.4: Let `S` be a scheme. Let `X` be a presheaf on
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
@[stacks 0AN1] #check (AlgebraicGeometry.IsAffineFormalAlgebraicSpace.tfae_spf :
  ∀ {S : Scheme.{u}}
    [HasWeakSheafify (full.bigTopology S) (Type (u + 1))]
    [HasPullbacks (Sheaf (full.bigTopology S) (Type (u + 1)))]
    (X : (full.bigSite S)ᵒᵖ ⥤ Type (u + 1)),
    List.TFAE [IsCountablyIndexedAffinePresheaf X, isColimitOfCountablyGeneratedSpf X,
      isColimitOfWeakIdealSequence X, isColimitOfCompleteLocallyNilpotentSequence X,
      isColimitOfQuotientInverseLimit X])
