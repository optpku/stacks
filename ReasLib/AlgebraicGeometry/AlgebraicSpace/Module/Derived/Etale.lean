/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ProjectionFormula
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.CellModel
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback.CellModel

/-! # Unbounded derived modules on small étale sites -/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleDerived

variable {S : Scheme.{u}}

/-- The standard unbounded derived category of modules over an étale coefficient sheaf. -/
abbrev category (X : AlgebraicSpace S)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :=
  RingedSite.NativeDerived.category.{u} (etaleRingedSite X A)

/-- The derived tensor bifunctor computed by the actual functorial cell complexes. -/
abbrev tensor (X : AlgebraicSpace S)
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u}) :
    category X A × category X A ⥤ category X A :=
  RingedSite.NativeDerived.CellTensor.functor A

variable {X Y : AlgebraicSpace S} (π : X ⟶ Y)
variable {A : Sheaf (smallEtaleTopology X) CommRingCat.{u}}
  {B : Sheaf (smallEtaleTopology Y) CommRingCat.{u}}
variable (φ : (etaleRingedSite Y B).structureSheaf ⟶
  (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)

/-- Degreewise inverse image of complexes of étale modules. -/
abbrev pullbackComplex :
    RingedSite.NativeDerived.CellTensor.Complex (J := smallEtaleTopology Y) B ⥤
      RingedSite.NativeDerived.CellTensor.Complex (J := smallEtaleTopology X) A :=
  @RingedSite.ToposHom.modulePullbackComplex (etaleRingedSite X A) (etaleRingedSite Y B)
    _ _ (toRingedToposHom π φ)
    (restrictScalars_toRingedToposHom_isRightAdjoint π φ)

/-- Unbounded derived inverse image computed by pulled-back functorial cell complexes. -/
abbrev pullback : category Y B ⥤ category X A :=
  @RingedSite.ToposHom.NativeDerived.CellPullback.functor
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ A B (toRingedToposHom π φ)
    (restrictScalars_toRingedToposHom_isRightAdjoint π φ)

end AlgebraicGeometry.AlgebraicSpace.EtaleDerived
