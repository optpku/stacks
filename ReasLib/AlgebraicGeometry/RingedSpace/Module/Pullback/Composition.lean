module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of module pullbacks on ringed spaces

This file specializes the canonical sheaf-of-modules identity and composition isomorphisms to
morphisms of ringed spaces.  It is the ringed-space analogue of the corresponding API for
schemes and ringed sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y Z : RingedSpace.{u}}

/-- Pullback of module sheaves along the identity morphism of a ringed space is canonically the
identity functor. -/
@[stacks 0H79 "identity module pullback"]
noncomputable abbrev pullbackIdIso (X : RingedSpace.{u}) :
    pullback (𝟙 X) ≅ 𝟭 X.Modules :=
  SheafOfModules.pullbackId X.ringCatSheaf

/-- Pullback of module sheaves along a composite of ringed-space morphisms is canonically
iterated pullback. -/
@[stacks 01UW "composition of module pullbacks"]
noncomputable abbrev pullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  (SheafOfModules.pullbackComp
    (toRingCatSheafHom g) (toRingCatSheafHom f)).symm

end AlgebraicGeometry.RingedSpace.Hom
