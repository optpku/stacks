/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- A complex over a Noetherian local ring is normalized dualizing when it is dualizing
and its canonical derived coextension to the residue field is the residue field in degree zero. -/
def IsNormalizedDualizing {A : Type u} [CommRing A]
    [hNoetherian : IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  IsDualizing K ∧
    Nonempty
      (((ModuleCat.derivedCoextensionOfScalars
          (algebraMap A (IsLocalRing.ResidueField A))).obj K) ≅
        ModuleCat.single0
          (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A)))

/-- Intrinsic normalization is equivalent to dualizingness together with the canonical
residue-field coextension being the residue field concentrated in degree zero. -/
theorem isNormalizedDualizing_iff {A : Type u} [CommRing A]
    [hNoetherian : IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsNormalizedDualizing K ↔
      IsDualizing K ∧
        Nonempty
          (((ModuleCat.derivedCoextensionOfScalars
              (algebraMap A (IsLocalRing.ResidueField A))).obj K) ≅
            ModuleCat.single0
              (ModuleCat.of (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField A))) :=
  Iff.rfl

end CategoryTheory.DerivedCategory
