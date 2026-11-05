/-
Copyright (c) 2026 ReasLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The identity-ring-map argument follows NYLL
8c1b16d10afaca09e0dc72753c6575e230d31a55,
Nyll/SchemeTheory/Modules/Tensor/Monoidal.lean.
See ReasLib/ThirdParty/NYLL for the retained Anthropic and NYLL notices.
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sheafification.Tensor

/-! # Tensor stability of module-sheafification equivalences on a scheme

This is a proved specialization of the general presheaf theorem to the
ordinary site of opens of any scheme. No field, curve, smoothness, or
properness assumption enters the proof. It supplies a stability proof,
without adding another tensor structure on module sheaves.
-/

@[expose] public section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The sheafification equivalences of module presheaves on a scheme are stable under tensor. -/
theorem presheafWeakEquivalences_isMonoidal (X : Scheme.{u}) :
    (((Opens.grothendieckTopology X).W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).IsMonoidal := by
  let α : X.sheaf.obj ⋙ forget₂ CommRingCat RingCat ⟶
      X.sheaf.obj ⋙ forget₂ CommRingCat RingCat := 𝟙 _
  letI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) α :=
    Presheaf.isLocallyInjective_of_injective _ α (fun _ => Function.injective_id)
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) α :=
    Presheaf.isLocallySurjective_of_surjective _ α (fun _ => Function.surjective_id)
  exact PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf_sameUniverse
    X.sheaf.obj X.ringCatSheaf α

end AlgebraicGeometry.Scheme.Modules
