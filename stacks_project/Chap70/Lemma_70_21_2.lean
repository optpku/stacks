module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.DVRCodimZero

/-!
# Noetherian DVR valuative criterion for separatedness

A quasi-separated, locally finite-type morphism of algebraic spaces into a locally
Noetherian target is separated if and only if uniqueness holds in valuative squares,
in DVR squares, or in DVR squares with codimension-zero generic image.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 70.21.2: For a quasi-separated, locally finite-type morphism of algebraic
spaces into a locally Noetherian target, separatedness is equivalent to valuative
uniqueness, DVR uniqueness, and DVR uniqueness at codimension-zero generic images. -/
@[stacks 0H1W] #check
  (AlgebraicGeometry.AlgebraicSpace.Separated.tfae_valuativeCriterion_dvr_codimZero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiSeparated f] [LocallyOfFiniteType f] [IsLocallyNoetherian Y],
      List.TFAE [Separated f, ValuativeCriterion.Uniqueness f,
        ValuativeCriterion.DVR.Uniqueness f,
        ValuativeCriterion.DVR.UniquenessAtCodimZero f])
