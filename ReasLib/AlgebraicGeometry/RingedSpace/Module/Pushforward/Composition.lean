module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of module pushforwards on ringed spaces

This file specializes the canonical sheaf-of-modules composition isomorphism to morphisms of
ringed spaces.  Its orientation starts at pushforward along the composite, as required by
right-derived composition comparisons.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The canonical morphism from the identity pushforward of a module sheaf to itself. -/
def idPushforwardHom {X : RingedSpace.{u}} (F : X.Modules) :
    ((𝟙 X) _*).obj F ⟶ F :=
  (pullbackIdIso X).inv.app (((𝟙 X) _*).obj F) ≫
    (pullbackPushforwardAdjunction (𝟙 X)).counit.app F

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y Z : RingedSpace.{u}}

/-- Pushforward of module sheaves along a composite of ringed-space morphisms is canonically
isomorphic to iterated pushforward. -/
@[stacks 01F5 "composition of module pushforwards"]
noncomputable abbrev pushforwardCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward (f ≫ g)) ≅ (pushforward f) ⋙ (pushforward g) :=
  (SheafOfModules.pushforwardComp
    (toRingCatSheafHom g) (toRingCatSheafHom f)).symm

end AlgebraicGeometry.RingedSpace.Hom
