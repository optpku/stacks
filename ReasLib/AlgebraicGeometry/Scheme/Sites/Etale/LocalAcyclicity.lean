/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.VanishingCycles
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

/-- The actual constant abelian étale sheaf with value ℤ/nℤ. -/
def constZModEtale (X : Scheme.{u}) (n : ℕ) : Coefficients X :=
  let hSheafify : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := by
    let hcolim : ∀ U : X.Etale,
        PreservesColimitsOfShape (X.smallEtaleTopology.Cover U)ᵒᵖ
          (CategoryTheory.forget AddCommGrpCat.{u + 1}) := fun U ↦
      @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) inferInstance _ _
        (@isFiltered_op_of_isCofiltered _ _
          (isCofiltered_of_semilatticeInf_nonempty (X.smallEtaleTopology.Cover U)))
    exact @HasSheafify.mk' _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _ _
      (@plusPlusAdjunction _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1}
        _ _ _ _ _ _ _ _ hcolim _)
      (@preservesFiniteLimits_presheafToSheaf _ _ _ _ _ _ _ _ _ _ _
        hcolim _ _ _ _ _)
  (@constantSheaf _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _
    hSheafify.isRightAdjoint).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))

/-- Regard an abelian étale sheaf as a derived object concentrated in degree zero. -/
abbrev etaleSheafInDegreeZero {X : Scheme.{u}} (F : Coefficients X) : Complexes X :=
  let hSheafify : HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1} := by
    let hcolim : ∀ U : X.Etale,
        PreservesColimitsOfShape (X.smallEtaleTopology.Cover U)ᵒᵖ
          (CategoryTheory.forget AddCommGrpCat.{u + 1}) := fun U ↦
      @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) inferInstance _ _
        (@isFiltered_op_of_isCofiltered _ _
          (isCofiltered_of_semilatticeInf_nonempty (X.smallEtaleTopology.Cover U)))
    exact @HasSheafify.mk' _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1} _ _
      (@plusPlusAdjunction _ _ X.smallEtaleTopology AddCommGrpCat.{u + 1}
        _ _ _ _ _ _ _ _ hcolim _)
      (@preservesFiniteLimits_presheafToSheaf _ _ _ _ _ _ _ _ _ _ _
        hcolim _ _ _ _ _)
  (@DerivedCategory.singleFunctor (Coefficients X) _
    (@sheafIsAbelian _ _ AddCommGrpCat.{u + 1} _ _ X.smallEtaleTopology hSheafify) _ 0).obj F

/-- Local acyclicity at a geometric point means that every canonical comparison
from its strict henselization to a geometric vanishing-cycle fiber is an isomorphism. -/
def LocallyAcyclicAt {X S : Scheme.{u}} (f : X ⟶ S) (xbar : GeometricPoint X)
    (K : Complexes X) : Prop :=
  ∀ tbar : GeometricPoint (strictHenselizationAt S (xbar.map f)),
    IsIso (EtaleVanishingCycles.alpha f xbar tbar K)

/-- Pointwise local acyclicity makes the intrinsic comparison an isomorphism
at every geometric point of the strict henselization of the base. -/
theorem LocallyAcyclicAt.isIso_comparison {X S : Scheme.{u}} (f : X ⟶ S)
    (xbar : GeometricPoint X) (K : Complexes X) (h : LocallyAcyclicAt f xbar K)
    (tbar : GeometricPoint (strictHenselizationAt S (xbar.map f))) :
    IsIso (EtaleVanishingCycles.alpha f xbar tbar K) := h tbar

/-- Local acyclicity relative to a derived étale coefficient object at all geometric points. -/
class LocallyAcyclicRelative {X S : Scheme.{u}} (f : X ⟶ S) (K : Complexes X) : Prop where
  /-- Pointwise local acyclicity for the same derived coefficient object. -/
  locallyAcyclicAt : ∀ xbar : GeometricPoint X, LocallyAcyclicAt f xbar K

/-- Relative local acyclicity supplies the property at each geometric point. -/
theorem locallyAcyclicAt_of_locallyAcyclicRelative {X S : Scheme.{u}}
    (f : X ⟶ S) (K : Complexes X) [LocallyAcyclicRelative f K] (xbar : GeometricPoint X) :
    LocallyAcyclicAt f xbar K := LocallyAcyclicRelative.locallyAcyclicAt xbar

/-- Relative local acyclicity is precisely its pointwise condition. -/
theorem locallyAcyclicRelative_iff {X S : Scheme.{u}} (f : X ⟶ S) (K : Complexes X) :
    LocallyAcyclicRelative f K ↔ ∀ xbar : GeometricPoint X, LocallyAcyclicAt f xbar K :=
  ⟨fun h ↦ h.locallyAcyclicAt, fun h ↦ ⟨h⟩⟩

/-- Universal relative local acyclicity uses actual derived inverse image in every square. -/
class UniversallyLocallyAcyclicRelative {X S : Scheme.{u}} (f : X ⟶ S)
    (K : Complexes X) : Prop where
  /-- All cartesian base changes are locally acyclic for the pulled-back coefficients. -/
  of_baseChange : ∀ {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S),
    IsPullback g' f' f g →
      LocallyAcyclicRelative f' ((derivedInverseImage g').obj K)

/-- The identity base change of a universally locally acyclic coefficient object. -/
instance locallyAcyclicRelative_of_universally {X S : Scheme.{u}}
    (f : X ⟶ S) (K : Complexes X) [UniversallyLocallyAcyclicRelative f K] :
    LocallyAcyclicRelative f K := sorry

/-- Ordinary local acyclicity tests the actual constant prime-to-characteristic coefficients. -/
class LocallyAcyclic {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- Constant-coefficient local acyclicity at every geometric point. -/
  locallyAcyclicAt_const : ∀ (xbar : GeometricPoint X) (n : ℕ), (n : xbar.K) ≠ 0 →
    LocallyAcyclicAt f xbar (etaleSheafInDegreeZero (constZModEtale X n))

/-- The pointwise constant-coefficient consequence of ordinary local acyclicity. -/
theorem locallyAcyclicAt_of_locallyAcyclic {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyAcyclic f] (xbar : GeometricPoint X) (n : ℕ)
    (hn : (n : xbar.K) ≠ 0) :
    LocallyAcyclicAt f xbar (etaleSheafInDegreeZero (constZModEtale X n)) :=
  LocallyAcyclic.locallyAcyclicAt_const xbar n hn

/-- A morphism is universally locally acyclic when all its cartesian base changes are. -/
class UniversallyLocallyAcyclic {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  /-- Ordinary local acyclicity of every cartesian base change. -/
  of_baseChange : ∀ {X' S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S),
    IsPullback g' f' f g → LocallyAcyclic f'

/-- Universal local acyclicity implies local acyclicity by the identity square. -/
instance instLocallyAcyclic_of_universally {X S : Scheme.{u}}
    (f : X ⟶ S) [UniversallyLocallyAcyclic f] : LocallyAcyclic f := sorry

end AlgebraicGeometry.Scheme
