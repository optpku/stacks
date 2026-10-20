module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.Algebra.Category.FGModuleCat.Basic

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [CommRing A]

/-- The underlying finite `A`-module at stage `n` of a sequential inverse system of finite
`A`-modules. -/
abbrev stageModule (F : SequentialInverseSystem (FGModuleCat A)) (n : ℕ) : Type u :=
  (F.obj (op n)).obj

/-- The successor transition map of a sequential inverse system of finite `A`-modules, viewed as
an `A`-linear map. -/
abbrev stepLinearMap (F : SequentialInverseSystem (FGModuleCat A)) (n : ℕ) :
    F.stageModule (n + 1) →ₗ[A] F.stageModule n :=
  ModuleCat.homEquiv (F.stepMap n).hom

end CategoryTheory.SequentialInverseSystem
