/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.LocalRepresentation
import StacksCheckRecall

@[expose] public section

/- Lemma 20.46.8: derived morphisms out of a strictly perfect complex admit local chain-map
representatives; a chain map that is zero in the derived category is locally null-homotopic. -/

@[stacks 08C9 "(1) open-cover representation"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.Representation.cover

@[stacks 08C9 "(1) point-neighborhood representation"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.Representation.atPoint

@[stacks 08C9 "(1) equality representation view"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.Representation.at_eq

@[stacks 08C9 "(2) open-cover null homotopy"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.NullHomotopy.cover_of_derived_zero

@[stacks 08C9 "(2) point-neighborhood null homotopy"]
#check
  @AlgebraicGeometry.RingedSpace.CochainComplex.IsStrictlyPerfect.NullHomotopy.at_of_derived_zero

#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsRepresentedOn
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsLocallyRepresentedAt
