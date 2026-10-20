/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Cover
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Locality

/-!
# Flatness of syntomic morphisms

Syntomic scheme morphisms are flat.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Syntomic

/-- A syntomic morphism of schemes is flat. -/
theorem flat (hf : Syntomic f) : Flat f := by
  rw [Scheme.Hom.flat_iff_affineOpen_appLE_flat]
  rw [Scheme.Hom.syntomic_iff_affineOpen_appLE_syntomic] at hf
  intro U hU V hV e
  exact RingHom.Syntomic.flat (hf hU hV e)

end Syntomic

/-- Syntomic morphisms canonically infer as flat. -/
instance instFlatOfSyntomic [hf : Syntomic f] : Flat f :=
  Syntomic.flat hf

end AlgebraicGeometry
