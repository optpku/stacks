/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.InternalHom
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
import StacksCheckRecall

@[expose] public section

-- Local instance justification (defeq pin): the imported ModuleDerived and localized ModuleCat aliases use the standard homotopy localization; this fallback is definitionally the same quotient as the named moduleCat_hasDerivedCategory and does not choose another derived model.
attribute [local instance] HasDerivedCategory.standard

/-!
# Lemma 20.46.11

The reusable ringed-site owner separates the existential-bound source statement from the
chosen-bound companion.  This chapter entry adds no local derived-category instance, notation,
or duplicate proof.
-/

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [RingedSite.Hom.ModuleDerived.KFlat.HomotopyTensorDescends
  (J := Opens.grothendieckTopology X) X.sheaf]
variable [RingedSite.Hom.ModuleDerived.KFlat.TensorDescends
  (J := Opens.grothendieckTopology X) X.sheaf]
variable [RingedSite.Hom.ModuleDerived.KFlat.IsLocalization
  (J := Opens.grothendieckTopology X) X.sheaf]

-- Use the same canonical K-flat tensor as the reusable ringed-site theorem.
attribute [local instance] RingedSite.Hom.ModuleDerived.monoidalCategory
variable [MonoidalClosed (DerivedCategory (Modules X))]

/- Lemma 20.46.11 (08I5): if `F` is bounded below, `E` is bounded above, and every term of `E`
is a retract of a finite free module sheaf, then `(ihom E).obj F` represents the derived internal
Hom from `E` to `F`. -/
@[stacks 08I5]
#check fun (E F : CochainComplex (Modules X) ℤ)
    (hF : ∃ a : ℤ, F.IsStrictlyGE a)
    (hE : ∃ b : ℤ, E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ,
      SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf (E.X i)) ↦
  RingedSite.CochainComplex.InternalHom.Canonical.represents_of_bounds E F hF hE hterms

/- The same result with chosen lower and upper bounds. -/
#check fun (E F : CochainComplex (Modules X) ℤ) {a b : ℤ}
    (hF : F.IsStrictlyGE a) (hE : E.IsStrictlyLE b)
    (hterms : ∀ i : ℤ,
      SheafOfModules.finiteFreeRetractModuleProperty X.ringCatSheaf (E.X i)) ↦
  RingedSite.CochainComplex.InternalHom.Canonical.represents_of_strictBounds E F hF hE hterms

/- The degreewise source condition is the shared finite-free-retract object property. -/
#check @SheafOfModules.finiteFreeRetractModuleProperty

end AlgebraicGeometry.RingedSpace
