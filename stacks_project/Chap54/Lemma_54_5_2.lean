module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized.Properties

universe u

/- Lemma 54.5.2 (1): The source of a normalized blowup of a Nagata scheme at a closed
point is normal. -/
@[stacks 0BFT] #check (AlgebraicGeometry.Scheme.NormalizedBlowup.source_isNormal :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.Scheme.Nagata X]
    (s : AlgebraicGeometry.Scheme.NormalizedBlowup X), s.source.isNormal)

/- Lemma 54.5.2 (2): The source of a normalized blowup of a Nagata scheme at a closed
point is Nagata. -/
@[stacks 0BFT] #check (AlgebraicGeometry.Scheme.NormalizedBlowup.source_isNagata :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.Scheme.Nagata X]
    (s : AlgebraicGeometry.Scheme.NormalizedBlowup X), AlgebraicGeometry.Scheme.Nagata s.source)

/- Lemma 54.5.2 (3): The normalized blowup morphism of a Nagata scheme at a closed
point is proper. -/
@[stacks 0BFT] #check (AlgebraicGeometry.Scheme.NormalizedBlowup.hom_isProper :
  ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.Scheme.Nagata X]
    (s : AlgebraicGeometry.Scheme.NormalizedBlowup X), AlgebraicGeometry.IsProper s.hom)
