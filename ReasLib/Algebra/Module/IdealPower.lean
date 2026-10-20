module

public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.Algebra.Module.IdealPower.BaseChange
public import ReasLib.Algebra.Module.IdealPower.TorsionIdeal
public import ReasLib.Algebra.Module.IdealPower.Directed
public import ReasLib.Algebra.Module.IdealPower.Hom
public import ReasLib.Algebra.Module.IdealPower.Functoriality
public import ReasLib.Algebra.Module.IdealPower.ModuleCat
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.Algebra.Module.IdealPower.Submodule
public import ReasLib.Algebra.Module.IdealPower.Submodule.Sequential
public import ReasLib.Algebra.Module.IdealPower.Submodule.Tensor
public import ReasLib.Algebra.Module.IdealPower.Cover
public import ReasLib.Algebra.Module.Submodule.DirectedColimit

/-!
# Ideal-power module API

The leaf files split the finite annihilator stages, the module predicate, and
the induced Hom/functoriality constructions.  Import this file when a
downstream development needs the complete ideal-power module interface.
-/
