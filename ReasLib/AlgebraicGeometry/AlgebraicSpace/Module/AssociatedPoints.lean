/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemePullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Stalk
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated and weakly associated points on algebraic spaces

A point of an algebraic space is weakly associated (resp. associated) to a
quasi-coherent module when the corresponding condition holds on étale scheme
charts, or equivalently for the maximal ideal of the étale local ring acting on
the étale module stalk.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A point of `|X|` is weakly associated to `F` on some étale scheme chart. -/
def existsEtaleWeakAss (F : X.Modules) (x : Points X) : Prop :=
  ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧
      u ∈ (pullbackToScheme a F).weakAss

/-- A point of `|X|` is weakly associated to `F` on every étale scheme chart. -/
def forallEtaleWeakAss (F : X.Modules) (x : Points X) : Prop :=
  ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a → Points.map a (ofOver.pointsEquiv U u) = x →
      u ∈ (pullbackToScheme a F).weakAss

/-- The maximal ideal of `𝒪_{X, x̄}` is weakly associated to the stalk `F_{x̄}` at every geometric
point over `x`. -/
def etaleStalkWeakAss (F : X.Modules) (x : Points X) : Prop :=
  ∀ xbar : GeometricPoint X, xbar.liesOver x →
    Ideal.IsWeaklyAssociatedToModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)
      (IsLocalRing.maximalIdeal (etaleLocalRing X xbar))

/-- A point of `|X|` is associated to `F` on some étale scheme chart. -/
def existsEtaleAss (F : X.Modules) (x : Points X) : Prop :=
  ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧
      u ∈ (pullbackToScheme a F).associatedPoints

/-- A point of `|X|` is associated to `F` on every étale scheme chart. -/
def forallEtaleAss (F : X.Modules) (x : Points X) : Prop :=
  ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
    Etale a → Points.map a (ofOver.pointsEquiv U u) = x →
      u ∈ (pullbackToScheme a F).associatedPoints

/-- The maximal ideal of `𝒪_{X, x̄}` is an associated prime of the stalk `F_{x̄}` at every geometric
point over `x`. -/
def etaleStalkAss (F : X.Modules) (x : Points X) : Prop :=
  ∀ xbar : GeometricPoint X, xbar.liesOver x →
    IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
      associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)

/-- Weak association on some étale scheme chart is equivalent to the existence of a chart and a
weakly associated point mapping to the given point. -/
theorem existsEtaleWeakAss_iff (F : X.Modules) (x : Points X) :
    existsEtaleWeakAss F x ↔
      ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧
          u ∈ (pullbackToScheme a F).weakAss :=
  Iff.rfl

/-- Weak association on every étale scheme chart means that each point above the given point on each
such chart is weakly associated to the pulled-back module. -/
theorem forallEtaleWeakAss_iff (F : X.Modules) (x : Points X) :
    forallEtaleWeakAss F x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.map a (ofOver.pointsEquiv U u) = x →
          u ∈ (pullbackToScheme a F).weakAss :=
  Iff.rfl

/-- The étale-stalk weak-association condition holds exactly when the maximal ideal is weakly
associated to the module stalk at every geometric point above the given point. -/
theorem etaleStalkWeakAss_iff (F : X.Modules) (x : Points X) :
    etaleStalkWeakAss F x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x →
        Ideal.IsWeaklyAssociatedToModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing X xbar)) :=
  Iff.rfl

/-- Association on some étale scheme chart is equivalent to the existence of a chart and an
associated point mapping to the given point. -/
theorem existsEtaleAss_iff (F : X.Modules) (x : Points X) :
    existsEtaleAss F x ↔
      ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧
          u ∈ (pullbackToScheme a F).associatedPoints :=
  Iff.rfl

/-- Association on every étale scheme chart means that each point above the given point on each such
chart is associated to the pulled-back module. -/
theorem forallEtaleAss_iff (F : X.Modules) (x : Points X) :
    forallEtaleAss F x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.map a (ofOver.pointsEquiv U u) = x →
          u ∈ (pullbackToScheme a F).associatedPoints :=
  Iff.rfl

/-- The étale-stalk association condition holds exactly when the maximal ideal is an associated
prime of the module stalk at every geometric point above the given point. -/
theorem etaleStalkAss_iff (F : X.Modules) (x : Points X) :
    etaleStalkAss F x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x →
        IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
          associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  Iff.rfl

/-- Weak association on some étale scheme chart is equivalent to weak association on every étale
scheme chart. -/
theorem existsEtaleWeakAss_iff_forallEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) : existsEtaleWeakAss F x ↔ forallEtaleWeakAss F x :=
  sorry

/-- Weak association on some étale scheme chart is equivalent to weak association of the étale-local
maximal ideal to the module stalk at every geometric point over `x`. -/
theorem existsEtaleWeakAss_iff_etaleStalkWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) : existsEtaleWeakAss F x ↔ etaleStalkWeakAss F x :=
  sorry

/-- Weak association of the étale-local maximal ideal at every geometric point over `x` is
equivalent to the same condition at some geometric point over `x`. -/
theorem etaleStalkWeakAss_iff_exists (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    etaleStalkWeakAss F x ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧
        Ideal.IsWeaklyAssociatedToModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing X xbar)) :=
  sorry

/-- Weak association on some étale scheme chart at the image of a geometric point is equivalent to
weak association of the étale-local maximal ideal to the module stalk at that geometric point. -/
theorem mem_weakAss_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) :
    existsEtaleWeakAss F xbar.image ↔
      Ideal.IsWeaklyAssociatedToModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)
        (IsLocalRing.maximalIdeal (etaleLocalRing X xbar)) :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart is equivalent to
association on every étale scheme chart. -/
theorem existsEtaleAss_iff_forallEtaleAss (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ forallEtaleAss F x :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart is equivalent to
association of the étale-local maximal ideal to the module stalk at every geometric point over `x`.
-/
theorem existsEtaleAss_iff_etaleStalkAss (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ etaleStalkAss F x :=
  sorry

/-- On a locally Noetherian algebraic space, association of the étale-local maximal ideal at every
geometric point over `x` is equivalent to the same condition at some geometric point over `x`. -/
theorem etaleStalkAss_iff_exists (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    etaleStalkAss F x ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧
        IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
          associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart at the image of
a geometric point is equivalent to association of the étale-local maximal ideal to the module stalk
at that geometric point. -/
theorem mem_associatedPoints_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (xbar : GeometricPoint X) :
    existsEtaleAss F xbar.image ↔
      IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
        associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart agrees with weak
association on some étale scheme chart. -/
theorem existsEtaleAss_iff_existsEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ existsEtaleWeakAss F x :=
  sorry

/-- For a quasi-coherent module on an algebraic space, weak association on some étale scheme chart,
weak association on every étale scheme chart, and weak association of the étale-local maximal ideal
to the geometric module stalk are equivalent. -/
@[stacks 0CTW]
theorem weakAss_etaleChart_tfae (F : X.Modules) [F.IsQuasicoherent] (x : Points X) :
    List.TFAE [existsEtaleWeakAss F x, forallEtaleWeakAss F x, etaleStalkWeakAss F x] :=
  sorry

/-- For a quasi-coherent module on a locally Noetherian algebraic space, weak association on some or
every étale scheme chart and weak association of the étale-local maximal ideal to the geometric
module stalk are equivalent to the three corresponding association conditions. -/
@[stacks 0CTW]
theorem associatedPoints_etaleChart_tfae (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    List.TFAE [existsEtaleWeakAss F x, forallEtaleWeakAss F x, etaleStalkWeakAss F x,
      existsEtaleAss F x, forallEtaleAss F x, etaleStalkAss F x] :=
  sorry

/-- Weak association on every étale scheme chart is equivalent to the étale-stalk maximal-ideal
condition. -/
theorem forallEtaleWeakAss_iff_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) : forallEtaleWeakAss F x ↔ etaleStalkWeakAss F x :=
  sorry

/-- On a locally Noetherian algebraic space, association on every étale scheme chart is equivalent
to the étale-stalk associated-prime condition. -/
theorem forallEtaleAss_iff_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    forallEtaleAss F x ↔ etaleStalkAss F x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
