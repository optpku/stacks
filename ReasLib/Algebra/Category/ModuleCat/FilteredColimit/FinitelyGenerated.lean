module

public import Mathlib.Algebra.Colimit.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Basic

@[expose] public section

universe u v

namespace ModuleCat

/-- The finitely generated submodule system of a module has the module itself as its colimit. -/
noncomputable def fgSystemColimitIso (R : Type u) (M : Type (max u v)) [Ring R] [AddCommGroup M]
    [Module R M] [DecidableEq (Submodule R M)] :
    ModuleCat.of R (Module.DirectLimit (fun N : {N : Submodule R M // N.FG} => N.1)
      (Module.fgSystem R M)) ≅ ModuleCat.of R M :=
  (Module.fgSystem.equiv R M).toModuleIso

/-- The colimit comparison restricts on each finitely generated stage to its submodule inclusion. -/
theorem fgSystemColimitIso_hom_of (R : Type u) (M : Type (max u v)) [Ring R] [AddCommGroup M]
    [Module R M] [DecidableEq (Submodule R M)] (N : {N : Submodule R M // N.FG}) :
    (fgSystemColimitIso R M).hom.hom ∘ₗ
        Module.DirectLimit.of R _ _ _ N = N.1.subtype := sorry

end ModuleCat
