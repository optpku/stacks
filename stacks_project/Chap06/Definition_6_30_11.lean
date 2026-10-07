module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import StacksCheckRecall

@[expose] public section

/- Definition 6.30.11 (1): a presheaf of modules over a ring-valued presheaf on a basis is the
canonical `PresheafOfModules` object, whose data are objectwise modules with semilinear
restriction maps. -/
@[stacks 009S "presheaves of modules on a basis"]
recall PresheafOfModules

/- Definition 6.30.11 (2): morphisms of presheaves of modules on a basis are the canonical
`PresheafOfModules.Hom` morphisms, given objectwise by linear maps compatible with restriction. -/
@[stacks 009S "morphisms of presheaves of modules on a basis"]
recall PresheafOfModules.Hom

/- Definition 6.30.11 (3): when the ring-valued presheaf is a sheaf, a sheaf of modules is the
canonical `SheafOfModules` object, whose underlying presheaf of abelian groups is a sheaf. -/
@[stacks 009S "sheaves of modules on a basis"]
recall SheafOfModules
