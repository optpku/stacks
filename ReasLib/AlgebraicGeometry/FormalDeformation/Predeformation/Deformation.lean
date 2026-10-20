/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger

/-!
# Deformation categories from Rim-Schlessinger groupoid fibrations
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- Over a locally Noetherian scheme, the predeformation projection of a category
fibred in groupoids satisfying the Rim-Schlessinger condition is a deformation
category at every finite-type field point and every chosen object over that point. -/
instance instIsDeformationCategory_predeformationFunctor
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (X : GroupoidsOver S) [HasRimSchlessinger X]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    Functor.IsDeformationCategory
      (predeformationFunctor X openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
