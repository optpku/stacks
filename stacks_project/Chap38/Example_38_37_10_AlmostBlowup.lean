/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.IsAlmostBlowupSquare :
  {X X' : Scheme.{u}} → (X' ⟶ X) → X.IdealSheafData → Prop)

#check (AlgebraicGeometry.isAlmostBlowupSquare_iff :
  ∀ {X X' : Scheme.{u}} (b : X' ⟶ X) (I : X.IdealSheafData),
    IsAlmostBlowupSquare b I ↔
      LocallyOfFinitePresentation I.subschemeι ∧
      IsLocallyPrincipalClosedSubscheme (I.comap b).subschemeι ∧
      IsProper b ∧ LocallyOfFinitePresentation b ∧
      IsBlowup (strictTransformFst b (I.comap b) (𝟙 X)) I)

end AlgebraicGeometry
