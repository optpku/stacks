/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.Gluing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Pushout.Gluing

#check (AlgebraicGeometry.Scheme.Pushout.Gluing.baseChange :
  ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [IsAffineHom f],
    Over (pushout i f) ⥤ CategoricalPullback (Over.pullback f) (Over.pullback i))

#check (AlgebraicGeometry.Scheme.Pushout.Gluing.glue :
  ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [IsAffineHom f],
    CategoricalPullback (Over.pullback f) (Over.pullback i) ⥤ Over (pushout i f))

#check (AlgebraicGeometry.Scheme.Pushout.Gluing.adjunction :
  ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [IsAffineHom f],
    AlgebraicGeometry.Scheme.Pushout.Gluing.glue i f ⊣
      AlgebraicGeometry.Scheme.Pushout.Gluing.baseChange i f)

/- Lemma 37.14.4: for a thickening `i : X ⟶ X'` and an affine morphism
`f : X ⟶ Y`, the unit of the adjunction from pushout gluing to base change over
`pushout i f` is an isomorphism. -/
@[stacks 07RV] #check (AlgebraicGeometry.Scheme.Pushout.Gluing.unitIsIso :
  ∀ {X X' Y : Scheme.{u}} (i : X ⟶ X') (f : X ⟶ Y)
    [IsThickening i] [IsAffineHom f],
    IsIso (AlgebraicGeometry.Scheme.Pushout.Gluing.adjunction i f).unit)

end AlgebraicGeometry.Scheme.Pushout.Gluing
