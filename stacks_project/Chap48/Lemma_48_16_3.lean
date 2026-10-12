/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 48.16.3: for composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` in
`Scheme.FiniteTypeSeparatedOver S`, there is a canonical natural isomorphism
`(f ≫ g) ! ≅ g ! ⋙ f !`. -/
@[stacks 0ATX] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.UpperShriekCompChoice.compIso :
    ∀ {S : Scheme.{u}} [IsNoetherian S]
      {X Y Z : Scheme.FiniteTypeSeparatedOver S}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      (C : Scheme.Compactification.Of.UpperShriekCompChoice f g),
      Scheme.Compactification.Of.upperShriek (f ≫ g)
          (Scheme.Compactification.Of.comp f g C.P_g C.P_bar) C.A_fg.plus ≅
        Scheme.Compactification.Of.upperShriek g C.P_g C.A_g.plus ⋙
          Scheme.Compactification.Of.upperShriek f C.P_f C.A_f.plus)
