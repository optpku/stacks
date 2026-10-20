/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Polarized.OverScheme
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.RingTheory.Noetherian.ULift

/-!
# Openness of versality for polarized proper schemes

The category fibred in groupoids of polarized proper schemes satisfies openness
of versality over `Spec ℤ` and after base change to any Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The category fibred in groupoids of polarized proper schemes satisfies
openness of versality over `Spec ℤ`. -/
instance instOpennessOfVersality : OpennessOfVersality toGroupoidsOverSpecZ :=
  sorry

/-- The category fibred in groupoids of polarized proper schemes after base
change to any Noetherian scheme satisfies openness of versality. -/
instance instOpennessOfVersality_over {S : Scheme.{u}} [IsNoetherian S] :
    OpennessOfVersality (toGroupoidsOver S) :=
  sorry

end AlgebraicGeometry.Polarized
