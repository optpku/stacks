module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ConstantGroup

/-! Compatibility checks for the constant group algebraic-space construction. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ConstantGroup
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

/-- The scheme-realization slice functor, in the constant-group compatibility namespace. -/
noncomputable abbrev AlgebraicGeometry.ConstantGroup.ofOverSlice (S : Scheme.{u}) :
    Over S ⥤ Over (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 S))) :=
  AlgebraicGeometry.AlgebraicSpace.SchemeRealization.ofOverSlice S

#check (AlgebraicGeometry.ConstantGroup.ofOverSlice :
  ∀ (S : Scheme.{u}), Over S ⥤ Over (AlgebraicGeometry.AlgebraicSpace.ofOver (Over.mk (𝟙 S))))
#check (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.ofOverPullback :
  ∀ {S : Scheme.{u}} (X Y : Over S), AlgebraicSpace S)
#check (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.ofOverPullbackHom :
  ∀ {S : Scheme.{u}} (X Y : Over S),
    Limits.pullback (toBase (AlgebraicGeometry.AlgebraicSpace.ofOver X))
      (toBase (AlgebraicGeometry.AlgebraicSpace.ofOver Y)) ⟶
      AlgebraicGeometry.AlgebraicSpace.SchemeRealization.ofOverPullback X Y)
#check (AlgebraicGeometry.ConstantGroup.space :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}),
    GroupAlgebraicSpace B)
#check (AlgebraicGeometry.ConstantGroup.space_X :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}),
    (AlgebraicGeometry.ConstantGroup.space B G).X =
      (Over.pullback (toBase B)).obj
        (Over.mk (toBase (AlgebraicGeometry.AlgebraicSpace.ofOver
          (AlgebraicGeometry.ConstantGroup.baseChange S G).X))))
#check (AlgebraicGeometry.ConstantGroup.space_left :
  ∀ {S : Scheme.{u}} (B : AlgebraicSpace S) (G : GrpCat.{u}),
    (AlgebraicGeometry.ConstantGroup.space B G).X.left =
      Limits.pullback
        (toBase (AlgebraicGeometry.AlgebraicSpace.ofOver
          (AlgebraicGeometry.ConstantGroup.baseChange S G).X)) (toBase B))
