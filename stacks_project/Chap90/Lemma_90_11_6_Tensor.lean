module

public import ReasLib.Algebra.Category.FGModuleCat.Tensor

/-!
# Tensoring finitely generated modules on the left

Restriction of `M ⊗[K] -` from `FGModuleCat K` to `ModuleCat K`, together with
the canonical comparison of a `K`-linear functor against tensoring by its value
on `K`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {K : Type u} [Field K]

/-
The canonical tensor comparison is available through this chapter module.
-/
#check (FGModuleCat.tensorNatTrans :
  ∀ (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K],
    FGModuleCat.tensoringLeft (L.obj (FGModuleCat.of K K)) ⟶ L)
