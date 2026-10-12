/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import Mathlib.RingTheory.Henselian
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import stacks_project.Chap59.Lemma_59_82_1
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Projective line over `Spec A`. -/
abbrev projectiveLineOverSpec (A : Type u) [CommRing A] : Scheme.{u} :=
  ProjectiveSpace 1 (Spec (CommRingCat.of A))

/-- Unfolding of `projectiveLineOverSpec`. -/
theorem projectiveLineOverSpec_eq (A : Type u) [CommRing A] :
    projectiveLineOverSpec A = ProjectiveSpace 1 (Spec (CommRingCat.of A)) :=
  sorry

/-- Closed fibre of `P^1_A → Spec A`. -/
abbrev projectiveLineClosedFiber (A : Type u) [CommRing A] [IsLocalRing A] : Scheme.{u} :=
  (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber (IsLocalRing.closedPoint A)

/-- Unfolding of `projectiveLineClosedFiber`. -/
theorem projectiveLineClosedFiber_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    projectiveLineClosedFiber A =
      (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiber
        (IsLocalRing.closedPoint A) :=
  sorry

/-- Closed-fibre inclusion `X0 ⟶ P^1_A`. -/
abbrev projectiveLineClosedFiberι (A : Type u) [CommRing A] [IsLocalRing A] :
    projectiveLineClosedFiber A ⟶ projectiveLineOverSpec A :=
  (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiberι (IsLocalRing.closedPoint A)

/-- Unfolding of `projectiveLineClosedFiberι`. -/
theorem projectiveLineClosedFiberι_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    projectiveLineClosedFiberι A =
      (ProjectiveSpace.toBase 1 (Spec (CommRingCat.of A))).fiberι
        (IsLocalRing.closedPoint A) :=
  sorry

/-- Lemma 59.85.2: if `A` is henselian local, `X = P^1_A`, `X0` is the closed
fibre, `ℓ` is prime, and `I` is an injective sheaf of `ZMod ℓ`-modules on
`X_étale`, then étale cohomology of the restriction of `I` to `X0` vanishes in
positive degrees. -/
@[stacks 0A5H]
theorem etaleCohomology_restrict_injective_eq_zero_of_projectiveLine_henselian
    {A : Type u} [CommRing A] [HenselianLocalRing A] (ℓ : ℕ) [Fact ℓ.Prime]
    [HasSheafify (projectiveLineOverSpec A).smallEtaleTopology RingCat.{u}]
    [HasSheafify (projectiveLineOverSpec A).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (projectiveLineOverSpec A).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (projectiveLineOverSpec A).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (projectiveLineOverSpec A).Etale]
    [(siteAbelianSectionsFunctor (projectiveLineOverSpec A).smallEtaleTopology
        (terminal (projectiveLineOverSpec A).Etale)).Additive]
    [HasSheafify (projectiveLineClosedFiber A).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (projectiveLineClosedFiber A).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (projectiveLineClosedFiber A).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (projectiveLineClosedFiber A).Etale]
    [(siteAbelianSectionsFunctor (projectiveLineClosedFiber A).smallEtaleTopology
        (terminal (projectiveLineClosedFiber A).Etale)).Additive]
    [((smallEtalePullback (projectiveLineClosedFiberι A)).sheafPushforwardContinuous
        AddCommGrpCat.{u} (projectiveLineOverSpec A).smallEtaleTopology
        (projectiveLineClosedFiber A).smallEtaleTopology).IsRightAdjoint]
    (I : SheafOfModules
      ((constantSheaf (projectiveLineOverSpec A).smallEtaleTopology RingCat.{u}).obj
        (.of (ULift.{u} (ZMod ℓ)))))
    [Injective I] {q : ℕ} (hq : 0 < q) :
    IsZero (etaleCohomology (projectiveLineClosedFiber A)
      ((etaleAbelianRestriction (projectiveLineClosedFiberι A)).obj
        ((SheafOfModules.toSheaf _).obj I)) q) :=
  sorry

end AlgebraicGeometry.Scheme.Etale
