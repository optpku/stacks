/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Adjunction
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The associated-module counit on an affine scheme

The affine tilde construction supplies an inverse to the associated-module
counit. Both functors and all comparison maps are specified; only their laws
are needed to identify this inverse with the counit.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting module sheaves along a scheme isomorphism gives an equivalence,
with inverse given by restriction along the inverse scheme morphism. -/
def restrictEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.inv) (restrictFunctor e.hom)
    ((restrictFunctorId (X := X)).symm ≪≫
      (restrictFunctorCongr e.hom_inv_id).symm ≪≫ restrictFunctorComp e.hom e.inv)
    ((restrictFunctorComp e.inv e.hom).symm ≪≫
      restrictFunctorCongr e.inv_hom_id ≪≫ restrictFunctorId (X := Y))

variable (S : Scheme.{u}) [IsAffine S]

/-- Global sections after restriction to the canonical spectrum recover
ordinary global sections, with the same coefficient ring. -/
def affineGlobalSectionsIso :
    restrictFunctor S.isoSpec.inv ⋙ moduleSpecΓFunctor ≅
      S.toRingedSpace.moduleGlobalSectionsFunctor :=
  NatIso.ofComponents (fun M ↦
    ModuleCat.isoMk
      (M.restrictAppIso S.isoSpec.inv ⊤ ≪≫
        (M.presheaf.mapIso (eqToIso
          (show S.isoSpec.inv ''ᵁ ⊤ = ⊤ by simp)).op).symm)
      (by sorry)) (by sorry)

/-- The associated-module functor on an affine scheme agrees with tilde
sheafification transported along its canonical spectrum isomorphism. -/
def associatedFunctorIso :
    RingedSpace.Module.Associated.functor (RingHom.id S.toRingedSpace.globalSectionsRing) ≅
      tilde.functor S.toRingedSpace.globalSectionsRing ⋙ restrictFunctor S.isoSpec.hom :=
  (RingedSpace.Module.Associated.idAdjunction S.toRingedSpace).leftAdjointUniq
    (((tilde.adjunction (R := S.toRingedSpace.globalSectionsRing)).comp
      (restrictEquivalence S.isoSpec).symm.toAdjunction).ofNatIsoRight
        (affineGlobalSectionsIso S))

/-- The inverse of the associated-module counit, transported from the affine
tilde counit through restriction and the global-sections comparison. -/
def associatedCounitInv (M : S.Modules) [hM : M.IsQuasicoherent] :
    M ⟶
      (RingedSpace.Module.Associated.functor
        (RingHom.id S.toRingedSpace.globalSectionsRing)).obj
          (S.toRingedSpace.moduleGlobalSectionsFunctor.obj M) :=
  (restrictEquivalence S.isoSpec).unitIso.hom.app M ≫
    (restrictFunctor S.isoSpec.hom).map
      (asIso (M.restrict S.isoSpec.inv).fromTildeΓ).inv ≫
    (tilde.functor S.toRingedSpace.globalSectionsRing ⋙ restrictFunctor S.isoSpec.hom).map
      ((affineGlobalSectionsIso S).hom.app M) ≫
    (associatedFunctorIso S).inv.app (S.toRingedSpace.moduleGlobalSectionsFunctor.obj M)

/-- On an affine scheme, the associated sheaf of the global sections of a
quasi-coherent module is identified with that module by the fixed counit.
Its inverse is transported from the proved affine tilde counit. -/
@[stacks 01IB]
def associatedCounitIso (M : S.Modules) (hM : M.IsQuasicoherent) :
    (RingedSpace.Module.Associated.functor (RingHom.id S.toRingedSpace.globalSectionsRing)).obj
      (S.toRingedSpace.moduleGlobalSectionsFunctor.obj M) ≅ M where
  hom := (RingedSpace.Module.Associated.idAdjunction S.toRingedSpace).counit.app M
  inv := associatedCounitInv S M (hM := hM)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward comparison is the original associated-module counit. -/
@[simp]
theorem associatedCounitIso_hom (M : S.Modules) (hM : M.IsQuasicoherent) :
    (associatedCounitIso S M hM).hom =
      (RingedSpace.Module.Associated.idAdjunction S.toRingedSpace).counit.app M := rfl

/-- The inverse comparison is the transported affine tilde inverse. -/
@[simp]
theorem associatedCounitIso_inv (M : S.Modules) (hM : M.IsQuasicoherent) :
    (associatedCounitIso S M hM).inv = associatedCounitInv S M (hM := hM) := rfl

/-- The associated-module counit is invertible on affine quasi-coherent modules. -/
theorem associatedCounit_isIso (M : S.Modules) (hM : M.IsQuasicoherent) :
    IsIso ((RingedSpace.Module.Associated.idAdjunction S.toRingedSpace).counit.app M) :=
  (associatedCounitIso S M hM).isIso_hom

end AlgebraicGeometry.Scheme.Modules
