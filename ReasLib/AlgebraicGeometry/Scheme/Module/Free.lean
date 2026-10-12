/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Presentation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Adjunction
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Free module sheaves on schemes

This module records freeness results for restrictions and affine quasicoherent module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restricting a free module sheaf along an open immersion preserves freeness. -/
instance restrict_obj_isFree_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [SheafOfModules.IsFree M] :
    SheafOfModules.IsFree ((restrictFunctor f).obj M) := by
  let g := AlgebraicGeometry.RingedSpace.opensRingedSiteHom f.toLRSHom.toShHom
  -- Local instance justification (proof-local temporary data): finality is used only for the restriction-pullback comparison.
  letI : g.base.Final := CategoryTheory.final_of_representablyFlat g.base
  have hPullback : SheafOfModules.IsFree ((pullback f).obj M) := by
    change SheafOfModules.IsFree (g.modulePullback.obj M)
    infer_instance
  -- Local instance justification (proof-local temporary data): install the derived pullback
  -- freeness only for transport across the restriction-pullback isomorphism.
  let _ : SheafOfModules.IsFree ((pullback f).obj M) := hPullback
  exact SheafOfModules.IsFree.of_iso ((restrictFunctorIsoPullback f).app M).symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.tilde

/-- The affine tilde sheaf of a free module is a free module sheaf. -/
instance instIsFreeOfModuleFree {R : CommRingCat.{u}} (M : ModuleCat R)
    [Module.Free R M] : SheafOfModules.IsFree (AlgebraicGeometry.tilde M) := by
  let I := Module.Free.ChooseBasisIndex R M
  let b := Module.Free.chooseBasis R M
  let α : R →+* (Spec R).toLocallyRingedSpace.toRingedSpace.globalSectionsRing :=
    (AlgebraicGeometry.Scheme.ΓSpecIso R).inv.hom
  let eModule : M ≅ (ModuleCat.free R).obj I := b.repr.toModuleIso
  let eTilde := (AlgebraicGeometry.tilde.associatedFunctorIso R).app M
  let eMap := (AlgebraicGeometry.RingedSpace.Module.Associated.functor α).mapIso eModule
  let eFree := AlgebraicGeometry.RingedSpace.Module.Associated.freeIso α I
  have hAssoc :
      SheafOfModules.IsFree
        (AlgebraicGeometry.RingedSpace.Module.Associated.obj α M) := by
    exact SheafOfModules.IsFree.of_iso (eMap ≪≫ eFree).symm
  -- Local instance justification (proof-local temporary data): install associated-sheaf
  -- freeness only for transport across the affine tilde comparison.
  let _ : SheafOfModules.IsFree
      (AlgebraicGeometry.RingedSpace.Module.Associated.obj α M) := hAssoc
  exact SheafOfModules.IsFree.of_iso eTilde

end AlgebraicGeometry.tilde

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasicoherent module sheaf on an affine scheme is free when its module of global sections
is free. -/
instance instIsFreeOfIsQuasicoherentOfModuleFree {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [F.IsQuasicoherent]
    [Module.Free R ((AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F)] :
    SheafOfModules.IsFree F := by
  let M := (AlgebraicGeometry.moduleSpecΓFunctor (R := R)).obj F
  have hTilde : SheafOfModules.IsFree (AlgebraicGeometry.tilde M) := by
    infer_instance
  -- Local instance justification (proof-local temporary data): install tilde freeness only for
  -- transport across affine quasicoherent reconstruction.
  let _ : SheafOfModules.IsFree (AlgebraicGeometry.tilde M) := hTilde
  let hIso : IsIso (fromTildeΓ (R := R) F) := inferInstance
  let e : AlgebraicGeometry.tilde M ≅ F :=
    @asIso _ _ _ _ (fromTildeΓ (R := R) F) hIso
  exact SheafOfModules.IsFree.of_iso e

end AlgebraicGeometry.Scheme.Modules
