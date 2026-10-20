module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Normalized.Properties

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 89.5.2 (1): The source of a normalized blowup of a Nagata algebraic space at a
closed point is normal. -/
@[stacks 0BHK] #check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.source_isNormal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    [AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [AlgebraicGeometry.AlgebraicSpace.IsNagata X]
    (s : AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup X),
    AlgebraicGeometry.AlgebraicSpace.IsNormal s.source)

/- Lemma 89.5.2 (2): The source of a normalized blowup of a Nagata algebraic space at a
closed point is Nagata. -/
@[stacks 0BHK] #check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.source_isNagata :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    [AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [AlgebraicGeometry.AlgebraicSpace.IsNagata X]
    (s : AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup X),
    AlgebraicGeometry.AlgebraicSpace.IsNagata s.source)

/- Lemma 89.5.2 (3): The normalized blowup morphism of a Nagata algebraic space at a
closed point is proper. -/
@[stacks 0BHK] #check (AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup.hom_isProper :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    [AlgebraicGeometry.AlgebraicSpace.IsDecent X]
    [AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [AlgebraicGeometry.AlgebraicSpace.IsNagata X]
    (s : AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup X),
    AlgebraicGeometry.AlgebraicSpace.Proper s.hom)
