/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening

#check (IsUniversalFirstOrder :
  {X : Scheme.{u}} → Thickening.Over X → Prop)

#check (isUniversalFirstOrder_iff :
  ∀ {X : Scheme.{u}} (T : Thickening.Over X),
    IsUniversalFirstOrder T ↔
      IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom) ∧
        ∀ (U : Thickening.Over X)
          [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
          (a : U.left ⟶ T.left), ∃! g : U ⟶ T, g.left = a)

#check (IsUniversalFirstOrder.existsUniqueLift :
  ∀ {X : Scheme.{u}} {T : Thickening.Over X} [IsUniversalFirstOrder T]
    (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (a : U.left ⟶ T.left), ∃! g : U ⟶ T, g.left = a)

#check (IsUniversalFirstOrder.instIsFirstOrderThickening :
  ∀ {X : Scheme.{u}} (T : Thickening.Over X) [IsUniversalFirstOrder T],
    IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom))

#check (IsUniversalFirstOrder.lift :
  ∀ {X : Scheme.{u}} {T : Thickening.Over X} [IsUniversalFirstOrder T]
    (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (_ : U.left ⟶ T.left), U ⟶ T)

#check (IsUniversalFirstOrder.lift_left :
  ∀ {X : Scheme.{u}} {T : Thickening.Over X} [IsUniversalFirstOrder T]
    (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (a : U.left ⟶ T.left), (IsUniversalFirstOrder.lift U a).left = a)

#check (IsUniversalFirstOrder.lift_unique :
  ∀ {X : Scheme.{u}} {T : Thickening.Over X} [IsUniversalFirstOrder T]
    (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (a : U.left ⟶ T.left) (g : U ⟶ T) (_ : g.left = a),
    g = IsUniversalFirstOrder.lift U a)

end AlgebraicGeometry.Thickening
