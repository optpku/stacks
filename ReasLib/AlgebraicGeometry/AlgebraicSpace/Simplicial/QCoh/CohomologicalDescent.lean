/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.EtaleDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.QCoh.Category

/-! # Quasi-coherent cohomological descent along fppf hypercoverings -/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- For an fppf hypercovering, the canonical map from a quasi-coherent module to the
right-derived direct image of its pullback along the total étale augmentation is invertible. -/
theorem toPushforwardDerived_isIso (ha : IsFppfHypercovering a)
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) [F.IsQuasicoherent] :
    IsIso (toPushforwardDerived a F) := sorry

/-- A registered fppf-hypercovering condition makes the derived comparison for every
quasi-coherent module an isomorphism. -/
instance toPushforwardDerived_isIso_of_fact [h : Fact (IsFppfHypercovering a)]
    (F : RingedSite.ModuleCat.{u} (spacesRingedSite X)) [F.IsQuasicoherent] :
    IsIso (toPushforwardDerived a F) :=
  toPushforwardDerived_isIso a h.out F

end AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleModuleDerived

end
