/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import ReasLib.AlgebraicGeometry.GroupScheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

noncomputable section

/-- Every stalk ring of a group scheme over a field has a unique minimal prime ideal. -/
theorem existsUniqueMinimalPrime_stalk
    (G : SchemeOverField k) [GrpObj G] (g : G.left) :
    ∃! p : Ideal (SchemeOverField.stalkRing G g),
      p ∈ minimalPrimes (SchemeOverField.stalkRing G g) := by
  -- TODO: identify the unique minimal prime at the identity stalk via
  -- `existsUniqueIrreducibleComponent_throughIdentity` and
  -- `PrimeSpectrum.localizationAtPrimeIrreducibleComponents`, transport to rational points by
  -- translation, and descend to arbitrary points with
  -- `FieldExtension.Stalk.Local.toSourceMap_faithfullyFlat`.
  sorry

end

end AlgebraicGeometry.GroupScheme
