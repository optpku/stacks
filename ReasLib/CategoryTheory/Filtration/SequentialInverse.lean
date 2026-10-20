/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.CategoryTheory.Limits.Presentation

@[expose] public section

/-!
# Sequential Inverse Filtrations

This leaf packages an object as the limit of a sequential inverse system with
short exact successive transition rows.  Both the allowed transition class and
the condition on successive kernels are parameters, so applications can supply
admissible epimorphisms, products, or other exact-category data.
-/

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- A sequential inverse filtration of `I` presents it as the limit of a tower whose consecutive
transition rows are short exact, have morphisms in `admissibleEpi`, and have kernels satisfying
`pieceProperty`. -/
structure SequentialInverseFiltration (I : C) (admissibleEpi : MorphismProperty C)
    (pieceProperty : C → Prop) where
  /-- The inverse system of quotient stages. -/
  tower : SequentialInverseSystem C
  /-- The initial quotient stage is zero. -/
  towerZero : IsZero (tower.obj (op 0))
  /-- The cone from the presented object to the quotient tower. -/
  toCone : (Functor.const ℕᵒᵖ).obj I ⟶ tower
  /-- The supplied cone is limiting. -/
  isLimit : IsLimit (Cone.mk I toCone)
  /-- The kernels of the consecutive transition maps. -/
  piece : ℕ → C
  /-- The inclusion of each kernel into the corresponding source quotient stage. -/
  inclusion : ∀ n : ℕ, piece n ⟶ tower.obj (op (n + 1))
  /-- Each kernel inclusion is killed by the corresponding transition map. -/
  zero_comp : ∀ n : ℕ, inclusion n ≫ tower.transitionMap (Nat.le_succ n) = 0
  /-- Each consecutive transition row is short exact. -/
  shortExact :
    ∀ n : ℕ,
      (ShortComplex.mk (inclusion n) (tower.transitionMap (Nat.le_succ n))
        (zero_comp n)).ShortExact
  /-- Consecutive transition maps lie in the designated class. -/
  admissible : ∀ n : ℕ, admissibleEpi (tower.transitionMap (Nat.le_succ n))
  /-- Each successive kernel has the designated property. -/
  pieceProperty : ∀ n : ℕ, pieceProperty (piece n)

namespace SequentialInverseFiltration

/-- The limiting cone supplied by a sequential inverse filtration. -/
abbrev cone {I : C} {admissibleEpi : MorphismProperty C} {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) : Cone F.tower :=
  Cone.mk I F.toCone

/-- The map from the presented object of a sequential inverse filtration to its `n`th quotient
stage. -/
abbrev coneApp {I : C} {admissibleEpi : MorphismProperty C} {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) (n : ℕ) :
    I ⟶ F.tower.obj (op n) :=
  F.toCone.app (op n)

/-- The quotient-stage maps of a sequential inverse filtration commute with the successor
transition maps. -/
@[reassoc]
theorem coneApp_succ_comp_transitionMap {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty)
    (n : ℕ) :
    F.coneApp (n + 1) ≫ F.tower.transitionMap (Nat.le_succ n) = F.coneApp n := sorry

/-- A sequential inverse filtration provides the limit of its quotient tower. -/
instance instHasLimit {I : C} {admissibleEpi : MorphismProperty C} {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) : HasLimit F.tower :=
  HasLimit.mk ⟨F.cone, F.isLimit⟩

/-- The chosen limit data supplied by a sequential inverse filtration. -/
abbrev hasLimit {I : C} {admissibleEpi : MorphismProperty C} {pieceProperty : C → Prop}
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty) : HasLimit F.tower :=
  F.instHasLimit

/-- The canonical comparison from an object presented by a sequential inverse filtration to the
categorical limit of its quotient tower. -/
noncomputable def limitComparison {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    I ≅ limit F.tower :=
  F.isLimit.conePointUniqueUpToIso (limit.isLimit F.tower)

/-- The limit isomorphism supplied by a sequential inverse filtration. -/
noncomputable abbrev limitIso {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty) :
    I ≅ limit F.tower :=
  F.limitComparison

/-- Construct a sequential inverse filtration from an ordinary limit presentation and the
successive short-exact transition data. -/
noncomputable def ofLimitIso {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (tower : SequentialInverseSystem C)
    (towerZero : IsZero (tower.obj (op 0))) [HasLimit tower] (limitIso : I ≅ limit tower)
    (piece : ℕ → C) (inclusion : ∀ n : ℕ, piece n ⟶ tower.obj (op (n + 1)))
    (zero_comp : ∀ n : ℕ, inclusion n ≫ tower.transitionMap (Nat.le_succ n) = 0)
    (shortExact : ∀ n : ℕ,
      (ShortComplex.mk (inclusion n) (tower.transitionMap (Nat.le_succ n))
        (zero_comp n)).ShortExact)
    (admissible : ∀ n : ℕ, admissibleEpi (tower.transitionMap (Nat.le_succ n)))
    (pieceCondition : ∀ n : ℕ, pieceProperty (piece n)) :
    SequentialInverseFiltration I admissibleEpi pieceProperty :=
  { tower := tower
    towerZero := towerZero
    toCone := ((LimitPresentation.limit tower).ofIso limitIso.symm).π
    isLimit := ((LimitPresentation.limit tower).ofIso limitIso.symm).isLimit
    piece := piece
    inclusion := inclusion
    zero_comp := zero_comp
    shortExact := shortExact
    admissible := admissible
    pieceProperty := pieceCondition }

/-- The limit comparison of a sequential inverse filtration has the supplied cone component at
each quotient stage. -/
@[reassoc]
theorem limitComparison_hom_π {I : C} {admissibleEpi : MorphismProperty C}
    {pieceProperty : C → Prop} (F : SequentialInverseFiltration I admissibleEpi pieceProperty)
    (n : ℕ) :
    F.limitComparison.hom ≫ limit.π F.tower (op n) = F.coneApp n := sorry

end SequentialInverseFiltration

end CategoryTheory
