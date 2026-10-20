/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.AffineComparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Bounded.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

/-!
# Finiteness properties of derived internal Hom

Pseudo-coherent or perfect source complexes give quasi-coherence and boundedness preservation
properties for derived internal Hom on schemes.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.InternalHom

/-- Derived internal Hom from a pseudo-coherent complex to a bounded-below complex with
quasi-coherent cohomology again has quasi-coherent cohomology. -/
theorem derivedQCoh_of_pseudoCoherent {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K)
    (hL : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj) :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)
      ((ihomOf H K).obj L.obj) := sorry

/-- Derived internal Hom from a pseudo-coherent complex to a bounded-below complex with
quasi-coherent cohomology is locally bounded below. -/
theorem locallyBoundedBelow_of_pseudoCoherent {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K)
    (hL : (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L.obj) :
    RingedSpace.ModuleDerived.IsLocallyBoundedBelow
      ((ihomOf H K).obj L.obj) := sorry

/-- Derived internal Hom from a perfect complex to a complex with quasi-coherent cohomology
again has quasi-coherent cohomology. -/
theorem derivedQCoh_of_perfect {X : Scheme.{u}}
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (L : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    DerivedCategory.cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)
      ((ihomOf H K).obj L.obj) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.InternalHom
