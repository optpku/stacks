module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening

/-- A thickening over `X` is universal to first order if its defining morphism is
first order and every map from the closed part of another first-order thickening
over `X` extends uniquely to a morphism of thickenings. -/
class IsUniversalFirstOrder {X : Scheme.{u}} (T : Thickening.Over X) : Prop where
  /-- The defining morphism of a universal first-order thickening is first order. -/
  isFirstOrder :
    IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom)
  /-- A prescribed map on the closed part extends uniquely to a morphism of
  first-order thickenings over the base. -/
  existsUniqueLift (U : Thickening.Over X)
      [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
      (a : U.left ⟶ T.left) :
      ∃! g : U ⟶ T, g.left = a

/-- The first-order and unique-lifting conditions defining a universal first-order
thickening. -/
theorem isUniversalFirstOrder_iff {X : Scheme.{u}} (T : Thickening.Over X) :
    IsUniversalFirstOrder T ↔
      IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom) ∧
        ∀ (U : Thickening.Over X)
          [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
          (a : U.left ⟶ T.left), ∃! g : U ⟶ T, g.left = a := sorry

namespace IsUniversalFirstOrder

/-- A universal first-order thickening has a first-order defining morphism. -/
instance instIsFirstOrderThickening {X : Scheme.{u}} (T : Thickening.Over X)
    [hT : IsUniversalFirstOrder T] :
    IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom) :=
  hT.isFirstOrder

/-- The chosen extension of a map on the closed part to a morphism of universal
first-order thickenings. -/
noncomputable def lift {X : Scheme.{u}} {T : Thickening.Over X}
    [IsUniversalFirstOrder T] (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (a : U.left ⟶ T.left) : U ⟶ T :=
  (existsUniqueLift U a).choose

/-- The chosen lift has the prescribed map on the closed part. -/
theorem lift_left {X : Scheme.{u}} {T : Thickening.Over X}
    [IsUniversalFirstOrder T] (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (a : U.left ⟶ T.left) :
    (lift U a).left = a := sorry

/-- Every lift with the prescribed map on the closed part is the chosen lift. -/
theorem lift_unique {X : Scheme.{u}} {T : Thickening.Over X}
    [IsUniversalFirstOrder T] (U : Thickening.Over X)
    [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map U.hom)]
    (a : U.left ⟶ T.left) (g : U ⟶ T) (hg : g.left = a) :
    g = lift U a := sorry

end IsUniversalFirstOrder

end AlgebraicGeometry.Thickening
