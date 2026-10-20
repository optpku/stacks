/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Parameters
import StacksCheckRecall

@[expose] public section

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}

/- Definition 10.60.10 (1): a system of parameters of a Noetherian local ring of dimension `d`
is a sequence `x : Fin d → maximalIdeal R` generating an ideal of definition. -/
@[stacks 00KU]
#check (IsLocalRing.IsSystemOfParameters : (Fin d → IsLocalRing.maximalIdeal R) → Prop)

#check (IsLocalRing.isSystemOfParameters_iff_of_ringKrullDim_eq :
  ringKrullDim R = d → ∀ x : Fin d → IsLocalRing.maximalIdeal R,
    IsLocalRing.IsSystemOfParameters x ↔ (IsLocalRing.parameterIdeal x).IsIdealOfDefinition)

/- Definition 10.60.10 (2): if some sequence `x : Fin d → maximalIdeal R` generates the maximal
ideal, then `R` is a regular local ring and `x` is a regular system of parameters. -/
@[stacks 00KU]
#check (IsRegularLocalRing.iff_exists_regularSystemOfParameters :
  ringKrullDim R = d →
    (IsRegularLocalRing R ↔
      ∃ x : Fin d → IsLocalRing.maximalIdeal R, IsLocalRing.IsRegularSystemOfParameters x))

#check (IsRegularLocalRing R : Prop)

#check (IsLocalRing.IsRegularSystemOfParameters : (Fin d → IsLocalRing.maximalIdeal R) → Prop)

#check (IsLocalRing.isRegularSystemOfParameters_iff_of_ringKrullDim_eq :
  ringKrullDim R = d → ∀ x : Fin d → IsLocalRing.maximalIdeal R,
    IsLocalRing.IsRegularSystemOfParameters x ↔
      IsLocalRing.parameterIdeal x = IsLocalRing.maximalIdeal R)

end
