/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Torsion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u v w t

namespace AlgebraicGeometry.Etale.TorsionOnCurve

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}

/-- Compatibility name for the coverwise `p`-power torsion condition. -/
public abbrev IsPPowerTorsion (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  IsLocallyPPowerTorsion p F

/-- Local `p`-power torsion means annihilation after passing to a cover. -/
public theorem isPPowerTorsion_iff (p : ℕ) (F : Sheaf J AddCommGrpCat.{u}) :
    IsPPowerTorsion p F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ cover : J.Cover U, ∀ arrow : cover.Arrow,
          ∃ n : ℕ, (p ^ n) • F.obj.map arrow.f.op s = 0 := Iff.rfl

/-- Compatibility name for local torsion of order invertible in the coefficient field.
In characteristic zero every nonzero natural order is allowed. -/
public abbrev IsPrimeToCharTorsion (k : Type t) [Field k]
    (F : Sheaf J AddCommGrpCat.{u}) : Prop :=
  IsLocallyPrimeToCharTorsion k F

/-- Prime-to-characteristic torsion uses local annihilators that are units in `k`. -/
public theorem isPrimeToCharTorsion_iff (k : Type t) [Field k]
    (F : Sheaf J AddCommGrpCat.{u}) :
    IsPrimeToCharTorsion k F ↔
      ∀ (U : C) (s : F.obj.obj (op U)),
        ∃ cover : J.Cover U, ∀ arrow : cover.Arrow,
          ∃ n : ℕ, n ≠ 0 ∧ IsUnit (n : k) ∧ n • F.obj.map arrow.f.op s = 0 := Iff.rfl

/-- The morphism `Spec k' ⟶ Spec k` induced by a field extension `k → k'`. -/
public def specMapOfAlgebra {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] :
    Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k'))

/-- Evaluation of `specMapOfAlgebra` is `Spec.map` of the ring map of the field extension. -/
public theorem specMapOfAlgebra_eq {k : Type u} [Field k] (k' : Type u) [Field k'] [Algebra k k'] :
    specMapOfAlgebra k' = Spec.map (CommRingCat.ofHom (algebraMap k k')) := rfl

variable {k : Type u} [Field k]
variable [∀ Y : Scheme.{u}, HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Y : Scheme.{u}, HasExt.{u} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u}]
variable [∀ {S T : Scheme.{u}} (f : T ⟶ S),
  ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    S.smallEtaleTopology T.smallEtaleTopology).IsRightAdjoint]

/-- Compatibility name for the eight canonical cohomological properties. This is a
predicate, with local torsion supplied separately to the theorems proving it. -/
public abbrev StatementsHold (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) : Prop :=
  CurveCohomology.Properties X F

/-- Canonical restriction of global degree-two étale cohomology to an open subscheme. -/
public def restrictH2AlongOpen (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] :
    F.H' 2 (globalEtale X.left) ⟶
      (((smallEtalePullback j).sheafPullback AddCommGrpCat.{u}
        X.left.smallEtaleTopology U.smallEtaleTopology).obj F).H' 2 (globalEtale U) :=
  cohomologyPullback j F 2

/-- Open restriction is the degree-two canonical cohomology pullback. -/
public theorem restrictH2AlongOpen_eq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] :
    restrictH2AlongOpen X F j = cohomologyPullback j F 2 := rfl

variable [IsAlgClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})

/-- Clause (1), proved from local torsion and the curve hypotheses. -/
public theorem StatementsHold.vanishing_gt_two_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    {q : ℕ} (hq : 2 < q) :
    IsZero (F.H' q (globalEtale X.left)) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).1 q hq

/-- Clause (2), with the additional affine hypothesis. -/
public theorem StatementsHold.vanishing_of_isAffine_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q) :
    IsZero (F.H' q (globalEtale X.left)) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.1 h_affine q hq

/-- Clause (3) applies only in positive characteristic. -/
public theorem StatementsHold.vanishing_of_pPowerTorsion_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    {p : ℕ} (hp_pos : 0 < p) (hp : ringChar k = p)
    (hF : IsPPowerTorsion p F) {q : ℕ} (hq : 1 < q) :
    IsZero (F.H' q (globalEtale X.left)) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.2.1
    p hp_pos hp hF q hq

/-- Clause (4), using canonical inverse images and finite locally constant sheaves. -/
public theorem StatementsHold.finite_of_constructible_primeToChar_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    (h_cons : IsConstructibleEtale
      (fun {Y} inclusion G ↦
        ((smallEtalePullback inclusion).sheafPullback AddCommGrpCat.{u}
          X.left.smallEtaleTopology Y.smallEtaleTopology).obj G)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F)
    (h_prime : IsPrimeToCharTorsion k F) (q : ℕ) :
    Finite (F.H' q (globalEtale X.left)) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.2.2.1
    h_cons h_prime q

/-- Clause (5), with canonical constructibility and properness over the ground field. -/
public theorem StatementsHold.finite_of_isProper_constructible_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    (h_proper : IsProper X.hom)
    (h_cons : IsConstructibleEtale
      (fun {Y} inclusion G ↦
        ((smallEtalePullback inclusion).sheafPullback AddCommGrpCat.{u}
          X.left.smallEtaleTopology Y.smallEtaleTopology).obj G)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F)
    (q : ℕ) :
    Finite (F.H' q (globalEtale X.left)) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.2.2.2.1
    h_proper h_cons q

/-- Clause (6) for the canonical pullback along a cartesian base-change projection. -/
public theorem StatementsHold.baseChange_iso_primeToChar_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    (h_prime : IsPrimeToCharTorsion k F)
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k')) (q : ℕ) :
    IsIso (cohomologyPullback π F q) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.2.2.2.2.1
    h_prime X' π h_baseChange q

/-- Clause (7) for the canonical pullback along a proper base-change square. -/
public theorem StatementsHold.baseChange_iso_of_isProper_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    (h_proper : IsProper X.hom)
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k')) (q : ℕ) :
    IsIso (cohomologyPullback π F q) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.2.2.2.2.2.1
    h_proper X' π h_baseChange q

/-- Clause (8) for canonical open restriction on degree-two cohomology. -/
public theorem StatementsHold.h2_restrict_surjective_apply
    (h_dim : topologicalKrullDim X.left ≤ 1) (h_torsion : IsLocallyTorsion F)
    {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] :
    Epi (restrictH2AlongOpen X F j) :=
  (CurveCohomology.Properties.ofIsLocallyTorsion X h_dim F h_torsion).2.2.2.2.2.2.2 j

end AlgebraicGeometry.Etale.TorsionOnCurve
