/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_15_2_Fiber
public import stacks_project.Chap71.Lemma_71_2_1_Pullback

/-!
# Étale-chart weak association for modules on algebraic spaces

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

/-- The maximal ideal of `𝒪_{X, x̄}` is weakly associated to the stalk `F_{x̄}` at every
geometric point over `x`. -/
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

/-- The maximal ideal of `𝒪_{X, x̄}` is an associated prime of the stalk `F_{x̄}` at every
geometric point over `x`. -/
def etaleStalkAss (F : X.Modules) (x : Points X) : Prop :=
  ∀ xbar : GeometricPoint X, xbar.liesOver x →
    IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
      associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)

/-- Unfolding of `existsEtaleWeakAss`. -/
theorem existsEtaleWeakAss_iff (F : X.Modules) (x : Points X) :
    existsEtaleWeakAss F x ↔
      ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧
          u ∈ (pullbackToScheme a F).weakAss :=
  sorry

/-- Unfolding of `forallEtaleWeakAss`. -/
theorem forallEtaleWeakAss_iff (F : X.Modules) (x : Points X) :
    forallEtaleWeakAss F x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.map a (ofOver.pointsEquiv U u) = x →
          u ∈ (pullbackToScheme a F).weakAss :=
  sorry

/-- Unfolding of `etaleStalkWeakAss`. -/
theorem etaleStalkWeakAss_iff (F : X.Modules) (x : Points X) :
    etaleStalkWeakAss F x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x →
        Ideal.IsWeaklyAssociatedToModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing X xbar)) :=
  sorry

/-- Unfolding of `existsEtaleAss`. -/
theorem existsEtaleAss_iff (F : X.Modules) (x : Points X) :
    existsEtaleAss F x ↔
      ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a ∧ Points.map a (ofOver.pointsEquiv U u) = x ∧
          u ∈ (pullbackToScheme a F).associatedPoints :=
  sorry

/-- Unfolding of `forallEtaleAss`. -/
theorem forallEtaleAss_iff (F : X.Modules) (x : Points X) :
    forallEtaleAss F x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.map a (ofOver.pointsEquiv U u) = x →
          u ∈ (pullbackToScheme a F).associatedPoints :=
  sorry

/-- Unfolding of `etaleStalkAss`. -/
theorem etaleStalkAss_iff (F : X.Modules) (x : Points X) :
    etaleStalkAss F x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x →
        IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
          associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  sorry

/-- Weak association on some étale scheme chart is equivalent to weak association on every
étale scheme chart. -/
theorem existsEtaleWeakAss_iff_forallEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    (x : Points X) : existsEtaleWeakAss F x ↔ forallEtaleWeakAss F x :=
  sorry

/-- Weak association on some étale scheme chart is equivalent to weak association of the
étale-local maximal ideal to the module stalk at every geometric point over `x`. -/
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

/-- Weak association on some étale scheme chart at the image of a geometric point is
equivalent to weak association of the étale-local maximal ideal to the module stalk at
that geometric point. -/
theorem mem_weakAss_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    (xbar : GeometricPoint X) :
    existsEtaleWeakAss F xbar.image ↔
      Ideal.IsWeaklyAssociatedToModule (etaleLocalRing X xbar) (stalkModuleCat xbar F)
        (IsLocalRing.maximalIdeal (etaleLocalRing X xbar)) :=
  sorry

/-- Association on some étale scheme chart is equivalent to association on every étale
scheme chart. -/
theorem existsEtaleAss_iff_forallEtaleAss (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ forallEtaleAss F x :=
  sorry

/-- Association on some étale scheme chart is equivalent to association of the étale-local
maximal ideal to the module stalk at every geometric point over `x`. -/
theorem existsEtaleAss_iff_etaleStalkAss (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ etaleStalkAss F x :=
  sorry

/-- Association of the étale-local maximal ideal at every geometric point over `x` is
equivalent to the same condition at some geometric point over `x`. -/
theorem etaleStalkAss_iff_exists (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    etaleStalkAss F x ↔
      ∃ xbar : GeometricPoint X, xbar.liesOver x ∧
        IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
          associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  sorry

/-- Association on some étale scheme chart at the image of a geometric point is equivalent
to association of the étale-local maximal ideal to the module stalk at that geometric
point. -/
theorem mem_associatedPoints_etaleStalk (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (xbar : GeometricPoint X) :
    existsEtaleAss F xbar.image ↔
      IsLocalRing.maximalIdeal (etaleLocalRing X xbar) ∈
        associatedPrimesOfModule (etaleLocalRing X xbar) (stalkModuleCat xbar F) :=
  sorry

/-- On a locally Noetherian algebraic space, association on some étale scheme chart agrees
with weak association on some étale scheme chart. -/
theorem existsEtaleAss_iff_existsEtaleWeakAss (F : X.Modules) [F.IsQuasicoherent]
    [IsLocallyNoetherian X] (x : Points X) :
    existsEtaleAss F x ↔ existsEtaleWeakAss F x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
