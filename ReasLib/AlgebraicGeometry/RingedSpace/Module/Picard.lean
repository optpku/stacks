/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Picard

/-!
# Picard group of a ringed space

The Picard group `Pic(X)` is the group of isomorphism classes of invertible `𝒪_X`-modules
under tensor product. It is the ringed-space specialization of
`SheafOfModules.RingedSite.PicardGroup`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The Picard group of a ringed space, obtained from the Picard group of its canonical
ringed site. -/
@[stacks 01CX]
abbrev PicardGroup (X : RingedSpace.{u}) :=
  SheafOfModules.RingedSite.PicardGroup (Opens.grothendieckTopology X) X.sheaf

namespace Modules

/-- The Picard class represented by an invertible module sheaf on a ringed space. -/
@[stacks 01CX "Picard class of an invertible module sheaf"]
noncomputable abbrev picardClass {X : RingedSpace.{u}}
    (L : X.Modules) [MonoidalCategory.isInvertibleObject L] :
    X.PicardGroup :=
  MonoidalCategory.PicardGroup.mk L

end Modules

namespace PicardGroup

/-- The chosen invertible module-sheaf representative of a Picard class. -/
@[stacks 01CX "representative of a ringed-space Picard class"]
noncomputable abbrev repr {X : RingedSpace.{u}} (x : X.PicardGroup) : X.Modules :=
  MonoidalCategory.PicardGroup.repr x

/-- The canonical comparison from the representative of an invertible module sheaf's Picard
class to that module sheaf. -/
@[stacks 01CX "representative comparison for a Picard class"]
noncomputable abbrev reprPicardClassIso {X : RingedSpace.{u}}
    (L : X.Modules) [MonoidalCategory.isInvertibleObject L] :
    repr (Modules.picardClass L) ≅ L :=
  MonoidalCategory.PicardGroup.reprMkIso L

/-- Two invertible module sheaves determine the same Picard class exactly when they are
isomorphic. -/
@[stacks 01CX "equality of Picard classes"]
theorem picardClass_eq_iff {X : RingedSpace.{u}}
    (L N : X.Modules) [MonoidalCategory.isInvertibleObject L]
    [MonoidalCategory.isInvertibleObject N] :
    Modules.picardClass L = Modules.picardClass N ↔ Nonempty (L ≅ N) := sorry

/-- The structure module represents the zero Picard class. -/
@[stacks 01CX "zero Picard class"]
theorem picardClass_unit {X : RingedSpace.{u}} :
    Modules.picardClass (𝟙_ X.Modules) = (0 : X.PicardGroup) := sorry

/-- An invertible module sheaf has zero Picard class exactly when it is isomorphic to the
structure module. -/
@[stacks 01CX "trivial ringed-space Picard class"]
theorem picardClass_eq_zero_iff {X : RingedSpace.{u}}
    (L : X.Modules) [MonoidalCategory.isInvertibleObject L] :
    Modules.picardClass L = (0 : X.PicardGroup) ↔
      Nonempty (L ≅ 𝟙_ X.Modules) := sorry

/-- Tensor product of invertible module sheaves represents addition of their Picard classes. -/
@[stacks 01CX "addition of Picard classes"]
theorem picardClass_tensor {X : RingedSpace.{u}}
    (L N : X.Modules) [MonoidalCategory.isInvertibleObject L]
    [MonoidalCategory.isInvertibleObject N] :
    Modules.picardClass (L ⊗ N) =
      Modules.picardClass L + Modules.picardClass N := sorry

/-- The representative of the zero Picard class is canonically the structure module. -/
@[stacks 01CX "representative of the zero Picard class"]
noncomputable abbrev reprZeroIso {X : RingedSpace.{u}} :
    repr (0 : X.PicardGroup) ≅ 𝟙_ X.Modules :=
  MonoidalCategory.PicardGroup.reprZeroIso

/-- The representative of a sum is canonically the tensor product of the representatives. -/
@[stacks 01CX "representative of a sum of Picard classes"]
noncomputable abbrev reprAddIso {X : RingedSpace.{u}} (x y : X.PicardGroup) :
    repr (x + y) ≅ repr x ⊗ repr y :=
  MonoidalCategory.PicardGroup.reprAddIso x y

/-- The representative of a negative Picard class is canonically the chosen tensor inverse. -/
@[stacks 01CX "representative of a negative ringed-space Picard class"]
noncomputable abbrev reprNegIso {X : RingedSpace.{u}} (x : X.PicardGroup) :
    repr (-x) ≅ MonoidalCategory.isInvertibleObject.inverse (repr x) :=
  MonoidalCategory.PicardGroup.reprNegIso x

end PicardGroup

/-- The Picard group `Pic(X)` of a ringed space: the group of isomorphism classes of
invertible `𝒪_X`-modules under tensor product. -/
scoped[RingedSpacePicard] notation:max "Pic(" X ")" =>
  AlgebraicGeometry.RingedSpace.PicardGroup X

end AlgebraicGeometry.RingedSpace
