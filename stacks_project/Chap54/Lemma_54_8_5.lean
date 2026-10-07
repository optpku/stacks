module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence.RationalSingularity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 54.8.5 (1): if reduction to rational singularities is possible for a
two-dimensional local normal Nagata domain `A`, then `Spec A` admits a finite sequence of
normalized blowups at closed points whose terminal scheme is normal and has rational
singularities at all closed points. -/
@[stacks 0B4P] #check
  (RationalSingularity.ReductionPossible.exists_normalizedBlowupSequence :
    ∀ (A : Type u) [CommRing A] [IsDomain A]
      [RationalSingularity.ReductionPossible A],
      ∃ (X : Scheme.{u})
        (s : Scheme.NormalizedBlowupSequence (Spec (.of A)) X),
        X.isNormal ∧
          ∀ x : X, x ∈ closedPoints X →
            IsRationalSingularity (X.presheaf.stalk x))

/- Lemma 54.8.5 (2): the composite of a positive-dimensional finite sequence of normalized
blowups over an integral Nagata scheme is a modification. -/
@[stacks 0B4P] #check
  (AlgebraicGeometry.Scheme.NormalizedBlowupSequence.toSource_isModification :
    ∀ {X Y : Scheme.{u}} [Scheme.Nagata X] [IsIntegral X]
      (s : Scheme.NormalizedBlowupSequence X Y),
      0 < topologicalKrullDim X → IsModification s.toSource)

/- Lemma 54.8.5 (3): the composite of a finite sequence of normalized blowups over a Nagata
ring is a closed immersion into a standard projective space over the affine base. -/
@[stacks 0B4P] #check
  (AlgebraicGeometry.Scheme.NormalizedBlowupSequence.exists_projectiveSpaceEmbedding :
    ∀ {A : Type u} [CommRing A] [NagataRing A] {X : Scheme.{u}}
      (s : Scheme.NormalizedBlowupSequence (Spec (.of A)) X),
      ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace.scheme A n),
        And (IsClosedImmersion i)
          ((i ≫ ProjectiveSpace.toSpec A n) = s.toSource))
