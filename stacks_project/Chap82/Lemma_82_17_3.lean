/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor.Cycle
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Torsor.HenselianLocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.AssociatedCycle
import StacksCheckRecall

/-! # Lemma 82.17.3

The Laurent relative spectrum of an invertible module, its tautological frame,
base change, cycle pullback, and henselian local-ring comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open IsLocalRing TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (L : X.Modules) [isInvertibleObject L]

/- Lemma 82.17.3 (1): the Laurent relative-spectrum projection is surjective. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.instSurjective_gmTorsorπ L :
  Surjective (gmTorsorπ L))

/- Lemma 82.17.3 (1): the projection is smooth. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.instSmooth_gmTorsorπ L :
  Smooth (gmTorsorπ L))

/- Lemma 82.17.3 (1): the projection is affine. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.instAffine_gmTorsorπ L :
  Affine (gmTorsorπ L))

/- Lemma 82.17.3 (1): the projection has relative dimension one. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.instRelativeDimension_gmTorsorπ L :
  RelativeDimension (gmTorsorπ L) 1)

/- Lemma 82.17.3 (2): the pullback of the line has its tautological trivialization. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorTriv L :
  (pullback (gmTorsorπ L)).obj L ≅ 𝟙_ (gmTorsor L).Modules)

section BaseChange

variable {Y : AlgebraicSpace S} (g : Y ⟶ X)

/- Lemma 82.17.3 (3): the relative spectrum commutes with arbitrary base change. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorPullbackIso g L :
  gmTorsor ((pullback g).obj L) ≅ Limits.pullback g (gmTorsorπ L))

/- Lemma 82.17.3 (3): the actual tautological trivialization commutes with base change. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorTriv_pullback g L :
  (gmTorsorTriv ((pullback g).obj L)).hom =
    (pullbackCompIso (gmTorsorπ ((pullback g).obj L)) g).hom.app L ≫
      eqToHom (congrArg (fun f ↦ (pullback f).obj L) (gmTorsorMap_comp_π g L)) ≫
      (pullbackCompIso (gmTorsorMap g L) (gmTorsorπ L)).inv.app L ≫
      (pullback (gmTorsorMap g L)).map (gmTorsorTriv L).hom ≫
      (PullbackTensor.unitIso (gmTorsorMap g L)).hom)

end BaseChange

section Cycles

variable {B : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Lemma 82.17.3 (4): flat pullback is injective on the integer-graded cycle groups. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.gmTorsorπ_flatPullbackHom_injective f δ L k :
  Function.Injective (Hom.flatPullbackHom f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k))

variable (Z : ClosedSubspace X)
variable (hZ : Hom.closedSubspaceDeltaDimension f δ Z ≤ (k : EInt))

/- Lemma 82.17.3 (6): inverse image raises the closed-subspace dimension bound by at most one. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.closedSubspaceDeltaDimension_inverseImage_le
    f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k Z hZ :
  Hom.closedSubspaceDeltaDimension (gmTorsorπ L ≫ f) δ
    (Z.inverseImageSubspace (gmTorsorπ L)) ≤ (k + 1 : EInt))

/- Lemma 82.17.3 (6): the inverse-image associated cycle equals flat pullback of the original cycle. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullback_closedSubspaceCycle
    f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k Z hZ :
  Hom.closedSubspaceCycle (gmTorsorπ L ≫ f) δ
    (Z.inverseImageSubspace (gmTorsorπ L)) (k + 1)
    (Hom.closedSubspaceDeltaDimension_inverseImage_le
      f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k Z hZ) =
  Hom.flatPullback f (gmTorsorπ L ≫ f) δ (gmTorsorπ L) 1 rfl k
    (Hom.closedSubspaceCycle f δ Z k hZ))

end Cycles

section Integral

variable (Z : ClosedSubspace X) [IsIntegral Z.X]

/- Lemma 82.17.3 (5): inverse image of every integral closed subspace remains integral. -/
@[stacks 0EQG] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isIntegral_inverseImage_gmTorsorπ L Z :
  IsIntegral (Z.inverseImageSubspace (gmTorsorπ L)).X)

end Integral

section Henselian

variable [IsDecent X] (ξ : Points X) (ξ' : Points (gmTorsor L))
variable (hξ' : Points.map (gmTorsorπ L) ξ' = ξ ∧
  IsGenericPoint ξ' (closure (Points.map (gmTorsorπ L) ⁻¹' {ξ})))

/- Lemma 82.17.3 (7): the canonical henselian ring map is flat at a generic fibre point. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorπ_henselianMap_flat L ξ ξ' hξ' :
  RingHom.Flat (HenselianFunctoriality.map (gmTorsorπ L) ξ' ξ hξ'.1))

/- Lemma 82.17.3 (7): the target maximal ideal is the extended source maximal ideal. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorπ_henselianMap_maximalIdeal L ξ ξ' hξ' :
  maximalIdeal (henselianLocalRing (gmTorsor L) ξ') =
    (maximalIdeal (henselianLocalRing X ξ)).map
      (HenselianFunctoriality.map (gmTorsorπ L) ξ' ξ hξ'.1))

/- Lemma 82.17.3 (7): the actual henselian residue-field extension is purely transcendental. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorπ_henselianMap_isPurelyTranscendental L ξ ξ' hξ' :
  (ResidueField.map (HenselianFunctoriality.map (gmTorsorπ L) ξ' ξ hξ'.1)).IsPurelyTranscendental)

/- Lemma 82.17.3 (7): the actual residue map identifies the target with a rational function field in one variable over the source. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.gmTorsorπ_henselianResidueField_ratFunc L ξ ξ' hξ' :
  ∃ e : RatFunc (ResidueField (henselianLocalRing X ξ)) ≃+*
      ResidueField (henselianLocalRing (gmTorsor L) ξ'),
    e.toRingHom.comp (algebraMap (ResidueField (henselianLocalRing X ξ))
      (RatFunc (ResidueField (henselianLocalRing X ξ)))) =
    ResidueField.map (HenselianFunctoriality.map (gmTorsorπ L) ξ' ξ hξ'.1))

/- Lemma 82.17.3 (7): the geometric residue-field transcendence degree is one. -/
@[stacks 0EQG] #check
  (AlgebraicGeometry.AlgebraicSpace.gmTorsorπ_residueFieldTrdeg L ξ ξ' hξ' :
  residueFieldTrdegAt (gmTorsorπ L) ξ' = 1)

end Henselian

end AlgebraicGeometry.AlgebraicSpace
