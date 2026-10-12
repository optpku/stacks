/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_93_1_LocalAcyclicity
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

@[expose] public section

universe u v w

namespace AlgebraicGeometry.Scheme

open EtaleVanishingCycles

/-- The geometric stalk in the coefficient universe of the actual derived étale category. -/
noncomputable def geometricStalkLarge {X : Scheme.{u}}
    (F : Coefficients X) (xbar : GeometricPoint X) : AddCommGrpCat.{u + 1} :=
  (@Scheme.pointSmallEtale X xbar.K inferInstance
    (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed)
    xbar.hom).presheafFiber.obj F.obj

/-- Geometric stalks of `F` are torsion of order prime to the residue characteristic of
the geometric point. -/
def geometricStalk_isPrimeToCharTorsion {X : Scheme.{u}}
    (F : Coefficients X) : Prop :=
  ∀ (xbar : GeometricPoint X) (a : (geometricStalkLarge F xbar : Type (u + 1))),
    ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ (n : xbar.K) ≠ 0

/-- Unfold the geometric-stalk prime-to-characteristic torsion condition. -/
theorem geometricStalk_isPrimeToCharTorsion_iff {X : Scheme.{u}}
    (F : Coefficients X) :
    geometricStalk_isPrimeToCharTorsion F ↔
      ∀ (xbar : GeometricPoint X) (a : (geometricStalkLarge F xbar : Type (u + 1))),
        ∃ n : ℕ, n ≠ 0 ∧ n • a = 0 ∧ (n : xbar.K) ≠ 0 :=
  Iff.rfl

/-- Lemma 59.93.3: a locally acyclic morphism is locally acyclic relative to a locally
constant abelian étale sheaf whose geometric stalks are torsion of order prime to the
residue characteristic. -/
@[stacks 0GJR]
instance locallyAcyclicRelative_of_locallyAcyclic
    {X S : Scheme.{u}} (f : X ⟶ S)
    (F : Coefficients X)
    [LocallyAcyclic f]
    [Sheaf.IsLocallyConstant F]
    [h_stalk : Fact (geometricStalk_isPrimeToCharTorsion F)] :
    LocallyAcyclicRelative f (etaleSheafInDegreeZero F) :=
  sorry

end AlgebraicGeometry.Scheme
