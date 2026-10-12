/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration.RegularSource
import StacksCheckRecall

open scoped AlgebraicGeometry

universe u

/- Lemma 54.13.1 (1): if a Noetherian integral scheme admits an alteration from a
regular integral scheme, then its normalization morphism is finite. -/
@[stacks 0BGG] #check (AlgebraicGeometry.IsAlteration.isFinite_normalizationTo :
  {X Y : AlgebraicGeometry.Scheme.{u}} →
    [AlgebraicGeometry.IsNoetherian Y] →
    [AlgebraicGeometry.IsIntegral Y] →
    [AlgebraicGeometry.IsIntegral X] →
    (f : X ⟶ Y) →
    [AlgebraicGeometry.IsAlteration f] →
    [AlgebraicGeometry.Scheme.Regular X] →
    AlgebraicGeometry.IsFinite Y.normalizationTo)

/- Lemma 54.13.1 (2): if a Noetherian integral scheme admits an alteration from a
regular integral scheme, then it has a dense regular open subscheme. -/
@[stacks 0BGG] #check (AlgebraicGeometry.IsAlteration.exists_dense_open_regular :
  {X Y : AlgebraicGeometry.Scheme.{u}} →
    [AlgebraicGeometry.IsNoetherian Y] →
    [AlgebraicGeometry.IsIntegral Y] →
    [AlgebraicGeometry.IsIntegral X] →
    (f : X ⟶ Y) →
    [AlgebraicGeometry.IsAlteration f] →
    [AlgebraicGeometry.Scheme.Regular X] →
    ∃ U : Y.Opens,
      Dense (U : Set Y) ∧ AlgebraicGeometry.Scheme.Regular U.toScheme)
