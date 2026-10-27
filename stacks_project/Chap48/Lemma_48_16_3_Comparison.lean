/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- This typed compatibility bridge preserves the historical import surface for
upper-shriek composition. -/
#check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice.compIso :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y Z : Scheme.FiniteTypeSeparatedOver S}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      (C : Scheme.Compactification.Of.UpperShriekCompChoice f g),
      Scheme.Compactification.Of.upperShriek (f ≫ g)
          (Scheme.Compactification.Of.comp f g C.P_g C.P_bar) C.A_fg.plus ≅
        Scheme.Compactification.Of.upperShriek g C.P_g C.A_g.plus ⋙
          Scheme.Compactification.Of.upperShriek f C.P_f C.A_f.plus)

/- Choice independence uses comparisons anchored to the actual refinement maps. -/
#check @Scheme.Compactification.Of.UpperShriekCompRefinement.upper_f_spec
#check @Scheme.Compactification.Of.UpperShriekCompRefinement.upper_g_spec
#check @Scheme.Compactification.Of.UpperShriekCompRefinement.upper_fg_spec
#check @Scheme.Compactification.Of.UpperShriekCompRefinement.upper_middle_spec
#check @Scheme.Compactification.Of.upperShriekCompIso_independent
