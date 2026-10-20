/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.RingedSpace.Basic
public import ReasLib.Topology.Sheaves.Ring.Definition
public import ReasLib.Topology.Sheaves.Pullback.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ring sheaves associated to ringed spaces

This module contains the ringed-space-level view of a commutative structure sheaf as a sheaf of
rings, together with the structure-sheaf maps induced by morphisms of ringed spaces.  It is
independent of sheaves of modules; module-specific functors belong in
`AlgebraicGeometry.RingedSpace.Module.Definition`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace TopCat.Sheaf

/-- A sheaf of commutative rings on a topological space, regarded as a ringed space. -/
abbrev toRingedSpace {X : TopCat.{u}} (O : X.Sheaf CommRingCat.{u}) :
    AlgebraicGeometry.RingedSpace.{u} :=
  { carrier := X
    presheaf := O.presheaf
    IsSheaf := O.2 }

end TopCat.Sheaf

namespace AlgebraicGeometry

namespace RingedSpace

/-- The structure sheaf of a ringed space, viewed as a sheaf of not-necessarily-commutative
rings. -/
abbrev ringCatSheaf (X : RingedSpace.{u}) : TopCat.Sheaf RingCat.{u} X :=
  TopCat.Sheaf.ringSheafOfComm X.sheaf

/-- The inverse-image open subset of a ringed-space morphism. -/
abbrev preimageOpen {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    (V : TopologicalSpace.Opens Y.carrier) : TopologicalSpace.Opens X.carrier :=
  (TopologicalSpace.Opens.map f.hom.base).obj V

end RingedSpace

namespace RingedSpace.Hom

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The structure-sheaf morphism `𝒪_Y ⟶ f_* 𝒪_X` attached to a morphism of ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a morphism of ringed spaces after forgetting commutativity. -/
noncomputable abbrev toRingCatSheafHom :
    Y.ringCatSheaf ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj X.ringCatSheaf :=
  TopCat.Sheaf.ringSheafOfCommMap (commRingSheafPushforwardMap f)

/-- The adjoint structure-sheaf morphism from the pullback of `Y.sheaf` to `X.sheaf`. -/
noncomputable abbrev inverseImageStructureSheafHomComm :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf ⟶ X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).homEquiv _ _).symm
    (commRingSheafPushforwardMap f)

namespace StructureSheaf

variable {Z : RingedSpace.{u}} (g : Y ⟶ Z)

/-- Pullback along `f` of the inverse-image structure-sheaf map of `g`. -/
noncomputable abbrev pullbackMap :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj Z.sheaf) ⟶
      (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj Y.sheaf :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).map
    (inverseImageStructureSheafHomComm g)

/-- The inverse-image structure-sheaf map on the iterated pullback source. -/
@[stacks 03D6 "inverse-image structure-sheaf composition"]
noncomputable abbrev compositeMap :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj Z.sheaf) ⟶ X.sheaf :=
  pullbackMap f g ≫ inverseImageStructureSheafHomComm f

/-- The canonical comparison from the iterated inverse image of a commutative ring sheaf to
its inverse image along the composite map. -/
@[stacks 03D6 "composition of inverse images of structure sheaves"]
noncomputable def compIso :
    (TopCat.Sheaf.pullback CommRingCat.{u} f.hom.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} g.hom.base).obj Z.sheaf) ≅
      (TopCat.Sheaf.pullback CommRingCat.{u} (f ≫ g).hom.base).obj Z.sheaf :=
  (TopCat.Sheaf.pullbackComp (A := CommRingCat.{u}) f.hom.base g.hom.base).app Z.sheaf

/-- The iterated inverse-image structure map is the composite structure map after transport
along `compIso`. -/
@[stacks 03D6 "compatibility of inverse-image structure-sheaf composition"]
theorem compositeMap_eq :
    compositeMap f g =
      (compIso f g).hom ≫ inverseImageStructureSheafHomComm (f ≫ g) := sorry

end StructureSheaf

end RingedSpace.Hom

end AlgebraicGeometry
