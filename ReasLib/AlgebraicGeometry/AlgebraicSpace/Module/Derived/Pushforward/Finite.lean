/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-! # Exact derived direct image for finite morphisms -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
variable {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
  {B : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
variable (φ : (etaleRingedSite Y B).structureSheaf ⟶
  (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)

/-- Degreewise direct image of the original unbounded module complex. -/
def pushforwardComplex :
    RingedSite.NativeDerived.CellTensor.Complex (J := smallEtaleTopology X) A ⥤
      RingedSite.NativeDerived.CellTensor.Complex (J := smallEtaleTopology Y) B :=
  @Functor.mapHomologicalComplex _ _ _ _ _ _ _ (toRingedToposHom π φ).modulePushforward
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
      (toRingedToposHom π φ).modulePushforward
      (RingedSite.ToposHom.modulePushforward_additive (toRingedToposHom π φ))) (up ℤ)

/-- Degreewise finite direct image is additive on maps of complexes. -/
theorem pushforwardComplex_additive : (pushforwardComplex π φ).Additive :=
  @Functor.map_homogical_complex_additive _ _ _ _ _ _ _
    (toRingedToposHom π φ).modulePushforward
    (RingedSite.ToposHom.modulePushforward_additive (toRingedToposHom π φ)) (up ℤ)

/-- Finite direct image preserves quasi-isomorphisms of arbitrary unbounded module complexes. -/
theorem pushforward_preservesQuasiIso
    {K L : RingedSite.NativeDerived.CellTensor.Complex (J := smallEtaleTopology X) A} (a : K ⟶ L)
    (ha : QuasiIso a) : QuasiIso ((pushforwardComplex π φ).map a) := sorry

/-- Finite derived direct image is localization of actual degreewise direct image. -/
def pushforward : category X A ⥤ category Y B :=
  Localization.lift (W := RingedSite.NativeDerived.CellTensor.quasiIso A)
    (pushforwardComplex π φ ⋙ RingedSite.NativeDerived.CellTensor.Q B)
    (fun _ _ a ha ↦ Localization.inverts (RingedSite.NativeDerived.CellTensor.Q B)
      (RingedSite.NativeDerived.CellTensor.quasiIso B) _
      (pushforward_preservesQuasiIso π φ a ha))
    (RingedSite.NativeDerived.CellTensor.Q A)

/-- Finite derived direct image on any complex is its degreewise direct image. -/
def pushforwardComputation :
    RingedSite.NativeDerived.CellTensor.Q A ⋙ pushforward π φ ≅
      pushforwardComplex π φ ⋙ RingedSite.NativeDerived.CellTensor.Q B :=
  Localization.fac _ _ _

/-- Localization of exact finite direct image is its right derived functor. -/
theorem pushforward_isRightDerived :
    (pushforward π φ).IsRightDerivedFunctor (pushforwardComputation π φ).inv
      (RingedSite.NativeDerived.CellTensor.quasiIso A) := sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleDerived
