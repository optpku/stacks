module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection

/-!
# Stalkwise regularity of sections

This file defines pointwise regularity of module sections and characterizes regular global
functions on a ringed space by their germs in every stalk.
-/

@[expose] public section

open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- A section is regular at `x` when multiplication by its germ is injective on the stalk. -/
def IsRegularSectionAt (ℒ : X.Modules) (s : ℒ.sections) (x : X) : Prop :=
  Function.Injective ((moduleStalkHom x (regularSectionHom ℒ s)).hom)

/-- Regularity at a point is precisely injectivity of the induced stalk-module map. -/
theorem isRegularSectionAt_iff_injective (ℒ : X.Modules) (s : ℒ.sections) (x : X) :
    IsRegularSectionAt ℒ s x ↔
      Function.Injective ((moduleStalkHom x (regularSectionHom ℒ s)).hom) := sorry

/-- A global function is a regular section of the structure module exactly when its germ acts
regularly on every stalk ring. -/
theorem isRegularStructureSection_iff_stalkwise
    (f : X.presheaf.obj (op ⊤)) :
    IsRegularSection (SheafOfModules.unit X.ringCatSheaf)
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
          (globalSectionMul f (SheafOfModules.unit X.ringCatSheaf))) ↔
      ∀ x : X,
        IsSMulRegular (X.presheaf.stalk x)
          (X.presheaf.germ ⊤ x (Set.mem_univ x) f) := sorry

end AlgebraicGeometry.RingedSpace
