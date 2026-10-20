module

public import ReasLib.CategoryTheory.Monoidal.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# Picard groups of schemes

This file is the scheme-level specialization of the Picard group of a commutative ringed site.
It keeps the generic construction as the unique data owner while exposing signatures in terms
of `X.Modules`, without leaking the opens-site presentation to scheme-level clients.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The Picard group of a scheme, formed from tensor-invertible sheaves of modules. -/
@[stacks 040C "Picard group of a scheme"]
abbrev PicardGroup (X : Scheme.{u}) :=
  MonoidalCategory.PicardGroup X.Modules

namespace Modules

/-- The Picard class represented by an invertible sheaf of modules on a scheme. -/
@[stacks 040C "Picard class of an invertible scheme module"]
noncomputable abbrev picardClass {X : Scheme.{u}}
    (L : X.Modules) [MonoidalCategory.isInvertibleObject L] :
    X.PicardGroup :=
  MonoidalCategory.PicardGroup.mk L

end Modules

namespace PicardGroup

/-- The chosen invertible scheme-module representative of a Picard class. -/
@[stacks 040C "representative of a scheme Picard class"]
noncomputable abbrev repr {X : Scheme.{u}} (x : X.PicardGroup) : X.Modules :=
  MonoidalCategory.PicardGroup.repr x

/-- The canonical comparison from the representative of an invertible scheme module's Picard
class to that module. -/
@[stacks 040C "scheme representative comparison"]
noncomputable abbrev reprPicardClassIso {X : Scheme.{u}}
    (L : X.Modules) [MonoidalCategory.isInvertibleObject L] :
    repr (Modules.picardClass L) ≅ L :=
  MonoidalCategory.PicardGroup.reprMkIso L

/-- Two invertible scheme modules represent the same Picard class exactly when they are
isomorphic. -/
@[stacks 040C "equality of scheme Picard classes"]
theorem picardClass_eq_iff {X : Scheme.{u}}
    (L N : X.Modules) [MonoidalCategory.isInvertibleObject L]
    [MonoidalCategory.isInvertibleObject N] :
    Modules.picardClass L = Modules.picardClass N ↔ Nonempty (L ≅ N) := sorry

/-- The tensor unit represents the zero Picard class of a scheme. -/
@[stacks 040C "zero scheme Picard class"]
theorem picardClass_unit {X : Scheme.{u}} :
    Modules.picardClass (𝟙_ X.Modules) = (0 : X.PicardGroup) := sorry

/-- An invertible scheme module has zero Picard class exactly when it is isomorphic to the
tensor unit. -/
@[stacks 040C "trivial scheme Picard class"]
theorem picardClass_eq_zero_iff {X : Scheme.{u}}
    (L : X.Modules) [MonoidalCategory.isInvertibleObject L] :
    Modules.picardClass L = (0 : X.PicardGroup) ↔
      Nonempty (L ≅ 𝟙_ X.Modules) := sorry

/-- Tensor product of invertible scheme modules represents addition of their Picard classes. -/
@[stacks 040C "addition of scheme Picard classes"]
theorem picardClass_tensor {X : Scheme.{u}}
    (L N : X.Modules) [MonoidalCategory.isInvertibleObject L]
    [MonoidalCategory.isInvertibleObject N] :
    Modules.picardClass (L ⊗ N) =
      Modules.picardClass L + Modules.picardClass N := sorry

/-- The representative of the zero scheme Picard class is canonically the tensor unit. -/
@[stacks 040C "representative of the zero scheme Picard class"]
noncomputable abbrev reprZeroIso {X : Scheme.{u}} :
    repr (0 : X.PicardGroup) ≅ 𝟙_ X.Modules :=
  MonoidalCategory.PicardGroup.reprZeroIso

/-- The representative of a sum is canonically the tensor product of the representatives. -/
@[stacks 040C "representative of a sum of scheme Picard classes"]
noncomputable abbrev reprAddIso {X : Scheme.{u}} (x y : X.PicardGroup) :
    repr (x + y) ≅ repr x ⊗ repr y :=
  MonoidalCategory.PicardGroup.reprAddIso x y

/-- The representative of a negative Picard class is canonically the chosen tensor inverse. -/
@[stacks 040C "representative of a negative scheme Picard class"]
noncomputable abbrev reprNegIso {X : Scheme.{u}} (x : X.PicardGroup) :
    repr (-x) ≅ MonoidalCategory.isInvertibleObject.inverse (repr x) :=
  MonoidalCategory.PicardGroup.reprNegIso x

end PicardGroup

end AlgebraicGeometry.Scheme
