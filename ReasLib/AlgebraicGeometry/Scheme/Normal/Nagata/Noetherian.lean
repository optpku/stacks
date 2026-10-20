/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic
public import ReasLib.RingTheory.Normal.Nagata.Characterization

@[expose] public section

/-!
# Noetherian consequences and characterization of Nagata schemes

The ring-level Nagata characterization is lifted to the affine-local scheme
owner in this module.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A Nagata scheme is locally Noetherian. -/
@[stacks 033U]
theorem isLocallyNoetherian_of_nagata (X : Scheme.{u}) (hX : Nagata X) :
    IsLocallyNoetherian X := sorry

/-- A scheme is Nagata exactly when it is locally Noetherian
and universally Japanese. -/
@[stacks 033Z]
theorem nagata_iff_isLocallyNoetherian_and_universallyJapanese (X : Scheme.{u}) :
    Nagata X ↔ IsLocallyNoetherian X ∧ UniversallyJapanese X := sorry

/-- A Nagata scheme is universally Japanese. -/
theorem universallyJapanese_of_nagata (X : Scheme.{u}) (hX : Nagata X) :
    UniversallyJapanese X := sorry

/-- Nagata schemes are locally Noetherian. -/
instance instIsLocallyNoetherianOfNagata (X : Scheme.{u}) [Nagata X] :
    IsLocallyNoetherian X := sorry

/-- Nagata schemes are universally Japanese. -/
instance instUniversallyJapaneseOfNagata (X : Scheme.{u}) [Nagata X] :
    UniversallyJapanese X := sorry

end AlgebraicGeometry.Scheme
