/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Properties

/-!
# Quasi-coherent modules on the small étale site

This module records closure properties of quasi-coherent module sheaves on the
small étale site of a scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.ObjectProperty
open AlgebraicGeometry
open Scheme.Etale.Small
open scoped SheafOfModules.RingedSite

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent

/-- Quasi-coherent modules on the small étale site are closed under colimits
of every universe-compatible shape. -/
@[instance]
theorem closedUnderColimitsOfShape (S : Scheme.{u})
    (J : Type v) [Category.{w} J] :
    IsClosedUnderColimitsOfShape
      (SheafOfModules.isQuasicoherent (smallStructureSheaf .etale S)) J := sorry

/-- A coproduct of quasi-coherent modules on the small étale site is
quasi-coherent. -/
@[instance]
theorem coproduct (S : Scheme.{u}) {ι : Type v}
    (F : ι → SheafOfModules (smallStructureSheaf .etale S))
    [HasCoproduct F] [∀ i, (F i).IsQuasicoherent] :
    (∐ F).IsQuasicoherent := sorry

/-- Quasi-coherent modules on the small étale site form a weak Serre class,
so they are closed under kernels, cokernels, and short-exact two-out-of-three
implications. -/
@[instance]
theorem isWeakSerreClass (S : Scheme.{u}) :
    IsWeakSerreClass
      (SheafOfModules.isQuasicoherent
        (smallCommRingedSite .etale S).structureSheaf) := sorry

/-- The internal Hom from a finitely presented module to a quasi-coherent
module on the small étale site is quasi-coherent. -/
@[instance]
theorem internalHom (S : Scheme.{u})
    (F G : RingedSite.ModuleCat.{u + 1} (smallCommRingedSite .etale S))
    [F.IsFinitePresentation] [G.IsQuasicoherent] :
    ((ihom F).obj G).IsQuasicoherent := sorry

/-- If a commutative local ring has Krull dimension zero, every module on the
small étale ringed site of its spectrum is quasi-coherent. -/
theorem all_isQuasicoherent_of_isLocalRing_of_ringKrullDim_eq_zero
    (R : Type u) [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 0) :
    ∀ F : RingedSite.ModuleCat.{u}
      (ringedSite (Spec (CommRingCat.of R))),
      F.IsQuasicoherent := sorry

end AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent
