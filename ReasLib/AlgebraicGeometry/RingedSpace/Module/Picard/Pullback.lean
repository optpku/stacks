module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Picard
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback on Picard groups of ringed spaces

Pullback of module sheaves is strong monoidal, so the generic Picard-group functor sends it to
an additive homomorphism.  This file exposes that construction in ringed-space language and
records its action on representatives, identities, and composites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X Y Z : RingedSpace.{u}}

/-- The Picard class represented by the pullback of an invertible module sheaf. -/
@[stacks 01CX "pullback of a Picard representative"]
noncomputable abbrev picardPullbackClass
    (f : X ⟶ Y) (L : Y.Modules) [isInvertibleObject L] :
    X.PicardGroup :=
  RingedSpace.Modules.picardClass ((pullback f).obj L)

/-- The additive homomorphism on Picard groups induced by pullback along a morphism of ringed
spaces. -/
@[stacks 01CX "pullback on Picard groups"]
noncomputable def picardPullback (f : X ⟶ Y) :
    Y.PicardGroup →+ X.PicardGroup :=
  MonoidalCategory.PicardGroup.map (pullback f)

/-- Pullback sends the class of an invertible module sheaf to the class of its pullback. -/
@[simp]
theorem picardPullback_apply_class
    (f : X ⟶ Y) (L : Y.Modules) [isInvertibleObject L] :
    picardPullback f (RingedSpace.Modules.picardClass L) =
      picardPullbackClass f L := sorry

/-- The representative of a pulled-back Picard class is canonically the pullback of its
representative. -/
@[stacks 01CX "representative of a pulled-back Picard class"]
noncomputable abbrev picardPullbackReprIso (f : X ⟶ Y) (x : Y.PicardGroup) :
    RingedSpace.PicardGroup.repr (picardPullback f x) ≅
      (pullback f).obj (RingedSpace.PicardGroup.repr x) :=
  MonoidalCategory.PicardGroup.reprMapIso (pullback f) x

/-- Pullback along the identity morphism acts as the identity on the Picard group. -/
@[simp]
theorem picardPullback_id :
    picardPullback (𝟙 X) = AddMonoidHom.id X.PicardGroup := sorry

/-- Pullback along the identity morphism fixes each Picard class. -/
@[simp]
theorem picardPullback_id_apply (x : X.PicardGroup) :
    picardPullback (𝟙 X) x = x := sorry

/-- Pullback on Picard groups is contravariantly compatible with composition. -/
@[simp]
theorem picardPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    picardPullback (f ≫ g) =
      (picardPullback f).comp (picardPullback g) := sorry

/-- Pullback of a Picard class along a composite is iterated pullback. -/
@[simp]
theorem picardPullback_comp_apply
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Z.PicardGroup) :
    picardPullback (f ≫ g) x =
      picardPullback f (picardPullback g x) := sorry

end AlgebraicGeometry.RingedSpace.Hom
