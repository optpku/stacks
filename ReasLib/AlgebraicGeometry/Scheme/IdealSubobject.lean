module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.ClosedSubspace.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.Scheme.Immersion

/-!
# Ideal subobjects of schemes

Ideal-sheaf data, kernel ideals of morphisms, and module-sheaf views are
connected here without changing the canonical Mathlib owner of closed
subschemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme

/-- An ideal subobject of a scheme, inherited from its underlying ringed space. -/
@[stacks 01C2 "scheme ideal subobject"]
abbrev IdealSubobject (X : Scheme.{u}) : Type (u + 1) :=
  RingedSpace.IdealSubobject X.toRingedSpace

/-- The module sheaf represented by an ideal subobject of a scheme, kept in the underlying
ringed-space module presentation that owns the subobject and its arrow. -/
@[stacks 01C2 "scheme ideal subobject module"]
noncomputable abbrev IdealSubobject.toModule
    {X : Scheme.{u}} (I : IdealSubobject X) : RingedSpace.Modules X.toRingedSpace :=
  RingedSpace.IdealSubobject.toModule I

end Scheme

namespace Scheme.Hom

/-- The kernel ideal of a scheme morphism as a subobject of its target structure sheaf. -/
@[stacks 01C2 "scheme kernel ideal subobject"]
noncomputable abbrev kernelIdealSubobject {X Z : Scheme.{u}} (i : Z ⟶ X) :
    Scheme.IdealSubobject X :=
  RingedSpace.Hom.kernelIdealSubobject i.toShHom

end Scheme.Hom

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The ideal subobject represented by ideal-sheaf data. -/
@[stacks 01C2 "ideal-sheaf data subobject"]
noncomputable abbrev toSubobject (I : X.IdealSheafData) : Scheme.IdealSubobject X :=
  Scheme.Hom.kernelIdealSubobject I.subschemeι

/-- The module sheaf represented by ideal-sheaf data, in the canonical ringed-space
presentation. -/
@[stacks 01C2 "ideal-sheaf data module"]
noncomputable abbrev toModule (I : X.IdealSheafData) :
    RingedSpace.Modules X.toRingedSpace :=
  I.toSubobject.toModule

/-- The module represented by `toSubobject` is canonically the kernel ideal sheaf. -/
@[stacks 01C2 "ideal-sheaf module comparison"]
noncomputable def toModuleIso (I : X.IdealSheafData) :
    I.toSubobject.toModule ≅ RingedSpace.Hom.kernelIdealSheaf I.subschemeι.toShHom :=
  RingedSpace.Hom.kernelIdealIso I.subschemeι.toShHom

/-- Under the comparison isomorphism, the subobject arrow is the canonical kernel inclusion. -/
@[reassoc (attr := simp), stacks 01C2 "ideal-sheaf module arrow comparison"]
theorem toModuleIso_hom_arrow (I : X.IdealSheafData) :
    I.toModuleIso.hom ≫
        RingedSpace.Hom.idealSheafι I.subschemeι.toShHom =
      I.toSubobject.arrow := sorry

/-- The inverse comparison carries the subobject arrow back to the kernel inclusion. -/
@[reassoc (attr := simp), stacks 01C2 "ideal-sheaf module inverse arrow comparison"]
theorem toModuleIso_inv_arrow (I : X.IdealSheafData) :
    I.toModuleIso.inv ≫ I.toSubobject.arrow =
      RingedSpace.Hom.idealSheafι I.subschemeι.toShHom := sorry

/-- The ideal-subobject inclusion followed by the defining quotient map is zero. -/
@[reassoc (attr := simp), stacks 01IO "ideal-subobject quotient vanishing"]
theorem toSubobject_arrow_comp_quotient (I : X.IdealSheafData) :
    I.toSubobject.arrow ≫ SheafOfModules.unitToPushforwardObjUnit
        (RingedSpace.Hom.toRingCatSheafHom I.subschemeι.toShHom) = 0 := sorry

/-- The canonical closed-subscheme inclusion has kernel ideal subobject `I.toSubobject`. -/
@[simp, stacks 01IO "closed-subscheme kernel ideal subobject"]
theorem kernelIdealSubobject_subschemeι (I : X.IdealSheafData) :
    LocallyRingedSpace.Hom.kernelIdealSubobject I.subschemeι.toLRSHom = I.toSubobject := sorry

/-- The canonical inclusion exhibits the subscheme as the closed subspace associated to
`I.toSubobject`. -/
@[stacks 01IO "closed subscheme associated to its ideal"]
theorem isAssociated_subschemeι (I : X.IdealSheafData) :
    LocallyRingedSpace.ClosedSubspace.IsAssociated
      I.subschemeι.toLRSHom I.toSubobject := sorry

end Scheme.IdealSheafData

namespace Scheme.Hom

/-- For a closed immersion, its ideal-sheaf datum recovers its kernel ideal subobject. -/
@[simp, stacks 01C2 "closed-immersion kernel ideal subobject"]
theorem ker_toSubobject {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    i.ker.toSubobject = i.kernelIdealSubobject := sorry

end Scheme.Hom

end AlgebraicGeometry
