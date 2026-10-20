module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszlo
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points

/-!
# Beauville–Laszlo glueing of algebraic spaces

For a ring homomorphism `R → R'` and `f : R`, write `X = Spec R`,
`U = Spec R_f`, `X' = Spec R'`, and `U' = Spec R'_f`. The category
`Spaces(U ← U' → X')` is the categorical pullback of `Over.pullback`
along `U' ⟶ U` and along `U' ⟶ X'`. The canonical functor
`Spaces/X ⥤ Spaces(U ← U' → X')` sends `Y ⟶ X` to
`(U ×_X Y, U' ×_X Y, X' ×_X Y)` by base change.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.functor :
  ∀ {R : Type u} (R' : Type u) [CommRing R] [CommRing R'] [Algebra R R'] (f : R),
    CategoryTheory.Over (AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.space R) ⥤
      AlgebraicGeometry.AlgebraicSpace.BeauvilleLaszloGlueing.category R' f)
