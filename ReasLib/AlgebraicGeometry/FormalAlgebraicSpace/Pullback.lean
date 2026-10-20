module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Pullbacks of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- The pullback of morphisms of formal algebraic spaces is a formal algebraic space. -/
instance IsFormalAlgebraicSpace.instPullback {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) : IsFormalAlgebraicSpace (pullback f g) :=
  sorry

/-- The base change of a locally of finite type morphism of formal algebraic spaces
to a locally Noetherian formal algebraic space is locally Noetherian. -/
instance IsLocallyNoetherian.instPullbackOfLocallyOfFiniteType {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Z] :
    IsLocallyNoetherian (pullback f g) :=
  sorry

namespace LocallyOfFiniteType

/-- A fibre product of a locally of finite type morphism of formal algebraic
spaces with a locally Noetherian object is locally Noetherian, for an
arbitrary `IsPullback` square. -/
theorem isLocallyNoetherian_of_isPullback {S : Scheme.{u}}
    {X Y Z P : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [IsFormalAlgebraicSpace P] {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X}
    {pZ : P ⟶ Z} (sq : IsPullback pX pZ f g) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Z] : IsLocallyNoetherian P :=
  sorry

end LocallyOfFiniteType

/-- The pullback of a locally Noetherian formal algebraic space along a
locally of finite type morphism of formal algebraic spaces is locally Noetherian. -/
instance IsLocallyNoetherian.instPullbackOfLocallyOfFiniteTypeRight {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [LocallyOfFiniteType g] [IsLocallyNoetherian X] :
    IsLocallyNoetherian (pullback f g) := by
  exact LocallyOfFiniteType.isLocallyNoetherian_of_isPullback
    (IsPullback.of_hasPullback f g).flip

end AlgebraicGeometry.FormalAlgebraicSpace
