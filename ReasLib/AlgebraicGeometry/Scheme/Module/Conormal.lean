/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Conormal.Map

/-!
# Conormal sheaves and comparison maps on schemes

This file specializes the kernel-cotangent conormal sheaf and its comparison map from ringed
spaces to schemes. The comparison is defined for an arbitrary commutative square; geometric
immersion hypotheses can be imposed by applications without changing the construction.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X Z' X' : Scheme.{u}}

/-- The conormal sheaf of a scheme morphism, formed from the kernel cotangent module of its
inverse-image structure-sheaf map. -/
noncomputable abbrev conormalSheaf (i : Z ⟶ X) : Z.Modules :=
  RingedSpace.Hom.conormalSheaf i.toShHom

namespace Conormal

variable {f : Z ⟶ Z'} {i : Z ⟶ X} {i' : Z' ⟶ X'} {g : X ⟶ X'}

set_option maxHeartbeats 4000000 in
/-- The canonical pullback comparison between conormal sheaves in a commutative square of
schemes. -/
noncomputable def map (sq : CommSq f i i' g) :
    (Scheme.Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i :=
  let shSq : CommSq f.toShHom i.toShHom i'.toShHom g.toShHom :=
    ⟨by
      rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
        ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, sq.w]⟩
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.base).homEquiv _ _)
      ((RingedSpace.Hom.StructureSheaf.compIso f.toShHom i'.toShHom).hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z.toSheafedSpace ⟶ X'.toSheafedSpace ↦ k.hom.base)
            shSq.w)).hom.app X'.sheaf ≫
        (RingedSpace.Hom.StructureSheaf.compIso i.toShHom g.toShHom).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.base).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom))
  SheafOfModules.RingedSite.Conormal.InverseImage.comparison
    (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
    (Opens.map f.base) middle (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)
      (RingedSpace.Hom.Conormal.structureSquare shSq)

set_option maxHeartbeats 4000000 in
/-- A scheme-level conormal comparison has the adjoint characterization inherited from the
underlying square of ringed spaces. -/
def IsMap (sq : CommSq f i i' g)
    (tau : (Scheme.Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i) : Prop :=
  let shSq : CommSq f.toShHom i.toShHom i'.toShHom g.toShHom :=
    ⟨by
      rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
        ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, sq.w]⟩
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.base).homEquiv _ _)
      ((RingedSpace.Hom.StructureSheaf.compIso f.toShHom i'.toShHom).hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z.toSheafedSpace ⟶ X'.toSheafedSpace ↦ k.hom.base)
            shSq.w)).hom.app X'.sheaf ≫
        (RingedSpace.Hom.StructureSheaf.compIso i.toShHom g.toShHom).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.base).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom))
  (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ tau =
    SheafOfModules.RingedSite.Conormal.InverseImage.comparisonAdjoint
      (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
      (Opens.map f.base) middle (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)
        (RingedSpace.Hom.Conormal.structureSquare shSq)

set_option maxHeartbeats 4000000 in
/-- On cotangent generators, the scheme conormal comparison applies the ambient structure map to
the kernel representative. -/
theorem map_toCotangent (sq : CommSq f i i' g) :
    let shSq : CommSq f.toShHom i.toShHom i'.toShHom g.toShHom :=
      ⟨by
        rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
          ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, sq.w]⟩
    ∀ (U : (Opens Z')ᵒᵖ)
      (x : conormalIdeal (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) U),
      let middle :=
        ((TopCat.Sheaf.pullbackPushforwardAdjunction
          CommRingCat.{u} f.toShHom.hom.base).homEquiv _ _)
          ((RingedSpace.Hom.StructureSheaf.compIso f.toShHom i'.toShHom).hom ≫
            (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
              (congrArg (fun k : Z.toSheafedSpace ⟶ X'.toSheafedSpace ↦ k.hom.base)
                shSq.w)).hom.app X'.sheaf ≫
            (RingedSpace.Hom.StructureSheaf.compIso i.toShHom g.toShHom).inv ≫
            (TopCat.Sheaf.pullback CommRingCat.{u} i.toShHom.hom.base).map
              (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom))
      SheafOfModules.RingedSite.Conormal.InverseImage.comparisonApp
          (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
          (Opens.map f.toShHom.hom.base) middle
          (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)
          (RingedSpace.Hom.Conormal.structureSquare shSq) U
          ((conormalIdeal
            (RingedSpace.Hom.inverseImageStructureSheafHomComm i'.toShHom) U).toCotangent x) =
        ((conormalSourcePresheafUnit
          (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)).app
          ((Opens.map f.toShHom.hom.base).op.obj U))
          ((conormalIdeal (RingedSpace.Hom.inverseImageStructureSheafHomComm i.toShHom)
            ((Opens.map f.toShHom.hom.base).op.obj U)).toCotangent
            ⟨(middle.hom.app U).hom x,
              SheafOfModules.RingedSite.Conormal.InverseImage.ideal_le_comap
                (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
                (Opens.map f.toShHom.hom.base) middle
                (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)
                (RingedSpace.Hom.Conormal.structureSquare shSq) U x.2⟩) :=
  let shSq : CommSq f.toShHom i.toShHom i'.toShHom g.toShHom :=
    ⟨by
      rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
        ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, sq.w]⟩
  RingedSpace.Hom.Conormal.map_toCotangent shSq

set_option maxHeartbeats 4000000 in
/-- The canonical scheme conormal comparison satisfies its adjoint characterization. -/
theorem map_isMap (sq : CommSq f i i' g) : IsMap sq (map sq) :=
  let shSq : CommSq f.toShHom i.toShHom i'.toShHom g.toShHom :=
    ⟨by
      rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
        ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, sq.w]⟩
  let middle :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction
      CommRingCat.{u} f.base).homEquiv _ _)
      ((RingedSpace.Hom.StructureSheaf.compIso f.toShHom i'.toShHom).hom ≫
        (TopCat.Sheaf.pullbackCongr (A := CommRingCat.{u})
          (congrArg (fun k : Z.toSheafedSpace ⟶ X'.toSheafedSpace ↦ k.hom.base)
            shSq.w)).hom.app X'.sheaf ≫
        (RingedSpace.Hom.StructureSheaf.compIso i.toShHom g.toShHom).inv ≫
        (TopCat.Sheaf.pullback CommRingCat.{u} i.base).map
          (RingedSpace.Hom.inverseImageStructureSheafHomComm g.toShHom))
  SheafOfModules.RingedSite.Conormal.InverseImage.comparison_adj
    (J := Opens.grothendieckTopology Z') (K := Opens.grothendieckTopology Z)
    (Opens.map f.base) middle (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)
      (RingedSpace.Hom.Conormal.structureSquare shSq)

set_option maxHeartbeats 4000000 in
/-- A scheme conormal comparison satisfying the adjoint characterization is the canonical map. -/
theorem eq_map (sq : CommSq f i i' g)
    {tau : (Scheme.Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i}
    (h_tau : IsMap sq tau) : tau = map sq := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  exact h_tau.trans (map_isMap sq).symm

set_option maxHeartbeats 4000000 in
/-- A commutative square of schemes has a unique conormal comparison satisfying the adjoint
characterization. -/
theorem existsUnique_map (sq : CommSq f i i' g) :
    ∃! tau : (Scheme.Modules.pullback f).obj (conormalSheaf i') ⟶ conormalSheaf i,
      IsMap sq tau :=
  ⟨map sq, map_isMap sq, fun tau h_tau ↦ eq_map sq h_tau⟩

end Conormal

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry

/-- Compatibility spelling for the conormal sheaf of a scheme immersion. -/
noncomputable abbrev immersionConormalSheaf {Z X : Scheme.{u}} (i : Z ⟶ X) : Z.Modules :=
  Scheme.Hom.conormalSheaf i

end AlgebraicGeometry
