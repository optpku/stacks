module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree
public import ReasLib.RingTheory.Flatness.LocallyFree

/-!
# Affine criteria for finite local freeness of scheme modules

This leaf compares the standard module properties of an `R`-module with the corresponding
properties of its associated quasi-coherent module on `Spec R`.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The associated module sheaf `M^~` on `Spec R` is of finite type exactly when
the `R`-module `M` is finite. -/
@[stacks 01PB]
theorem tilde_isFiniteType_iff_module_finite
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFiniteType (tilde M) ↔ Module.Finite R M := sorry

/-- The associated module sheaf `M^~` on `Spec R` is of finite presentation
exactly when the `R`-module `M` is finitely presented. -/
@[stacks 01PC]
theorem tilde_isFinitePresentation_iff_module_finitePresentation
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFinitePresentation (tilde M) ↔ Module.FinitePresentation R M := sorry

/-- The associated module sheaf of a finitely presented module is finitely presented. -/
instance instIsFinitePresentationTilde
    {R : CommRingCat.{u}} (M : ModuleCat R) [Module.FinitePresentation R M] :
    SheafOfModules.IsFinitePresentation (tilde M) := sorry

/-- The associated module sheaf `M^~` on `Spec R` is flat exactly when the
`R`-module `M` is flat. -/
@[stacks 05P0]
theorem tilde_isFlat_iff_module_flat
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFlat (X := (Spec R).toRingedSpace) (tilde M) ↔
      Module.Flat R M := sorry

/-- The associated module sheaf `M^~` on `Spec R` is locally free exactly
when the `R`-module `M` is locally free. -/
@[stacks 05JM]
theorem tilde_isLocallyFree_iff_module_locallyFree
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsLocallyFree
      (J := Opens.grothendieckTopology (Spec R).toRingedSpace)
      (R := (Spec R).toRingedSpace.ringCatSheaf) (tilde M) ↔
      Module.LocallyFree R M := sorry

/-- The associated module sheaf `M^~` on `Spec R` is finite locally free
exactly when the `R`-module `M` is finite locally free. -/
@[stacks 05JM]
theorem tilde_isFiniteLocallyFree_iff_module_finiteLocallyFree
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFiniteLocallyFree (tilde M) ↔
      Module.FiniteLocallyFree R M := sorry

end AlgebraicGeometry.Scheme.Modules
