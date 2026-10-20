/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Quotient.Stalk
import StacksCheckRecall

/-!
# Modules over quotient structure sheaves

The reusable owner works on an arbitrary ringed site. The generic quotient construction uses the
sectionwise predicate `IdealSheaf.IsAnnihilated I F`.
The ringed-space bridge identifies it with the source hypothesis `I ≤ Ann(F)` and exposes the
resulting quotient module without asking downstream users to unfold section ideals.
-/

@[expose] public section

open CategoryTheory

/- Lemma 17.23.3 (0H2K) (1): if `I ≤ Ann(F)`, then `F` carries its canonical module structure
over the genuine quotient sheaf `𝒪_X / I`. -/
@[stacks 0H2K "module structure over the quotient by an annihilating ideal sheaf"]
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.descendOfLE

/- The generic ringed-site owner packages the same construction using the sectionwise
`IdealSheaf.IsAnnihilated I F` predicate. -/
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.descend

/- The quotient ring sheaf comes with its canonical locally surjective projection, whose kernel
is exactly `I`. -/
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.projection
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.projection_isLocallySurjective
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.kernelIdealSubobject_projection

/- Lemma 17.23.3 (0H2K) (2): on stalks, the descended scalar action agrees with the usual module
structure over `𝒪_{X,x} / I_x`. -/
@[stacks 0H2K "quotient module structure agrees with the stalkwise construction"]
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.Stalk.forget_smul_projection

/- Taking a stalk of the genuine quotient sheaf gives the ordinary quotient by the image of the
ideal-sheaf stalk; this identification carries the sheaf projection and projected germs to the
ordinary quotient map. -/
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.stalkEquiv
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.stalkEquiv_projectionStalk
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.stalkEquiv_germ_projection

/- The source hypothesis is canonically equivalent to the generic sectionwise condition, and can
be passed directly to the quotient-module constructor. -/
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.le_annihilator_iff
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.descendOfLE

/- Quotienting by the full annihilator needs no separately supplied containment proof. -/
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.annihilator_isAnnihilated
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.descendAnnihilator
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.forgetIsoAnnihilator

/- The formal-language version of containment in the annihilator and its pointwise ideal form. -/
#check @SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
#check @SheafOfModules.RingedSite.IdealSheaf.isAnnihilated_iff

/- The descended module has the original underlying additive sheaf, and the projected scalar
action is the original action. -/
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.forgetIso
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.smul_projection
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.forgetIsoOfLE
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.smul_projection_of_le

/- The same compatibility is available together with the descended stalk object itself. -/
#check @AlgebraicGeometry.RingedSpace.IdealSheaf.Quotient.descendStalk

/- Before sheafification, the quotient action is already restriction-compatible and uniquely
determined on the fixed additive groups of sections. -/
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.map_act
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.act_projection
#check @SheafOfModules.RingedSite.IdealSheaf.Quotient.act_unique
