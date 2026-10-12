/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_91_12_BaseChange
public import ReasLib.CategoryTheory.Adjunction.Derived.Bounded
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf
open CategoryTheory.Adjunction.Derived.Plus

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- The unit of the bounded-below derived adjunction `p⁻¹ ⊣ Rp_*` on `D⁺` of abelian
small-étale sheaves. -/
noncomputable def etaleDerivedAdjunctionUnit {Z X : Scheme.{u}} (p : Z ⟶ X)
    [(abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    E ⟶ (etaleDerivedPushforward p).obj ((etaleDerivedInverseImage p).obj E) :=
  (adjunction (etalePullbackExact p) (abelianPushforwardAlong p)
      ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology)).unit.app E

/-- `etaleDerivedAdjunctionUnit` is the component of the bounded-below derived adjunction unit. -/
theorem etaleDerivedAdjunctionUnit_eq {Z X : Scheme.{u}} (p : Z ⟶ X)
    [(abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) :
    etaleDerivedAdjunctionUnit p E =
      (adjunction (etalePullbackExact p) (abelianPushforwardAlong p)
          ((smallEtalePullback p).sheafAdjunctionContinuous AddCommGrpCat.{u}
            X.smallEtaleTopology Z.smallEtaleTopology)).unit.app E := sorry

end AlgebraicGeometry.Scheme.Etale

end

end
