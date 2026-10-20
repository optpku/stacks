/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap50.Remark_50_14_2_ChernAction
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.DerivedDecomposition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open RingedSite.Hom
open AlgebraicGeometry.Scheme.DeRham.DerivedPushforward
open scoped MonoidalCategory TensorProduct

noncomputable section

-- Local instance justification (defeq pin): the shifted pullback/action formula uses the same canonical total-derived direct-image shift as its components.
attribute [local instance] AlgebraicGeometry.Scheme.DeRham.CanonicalTensor.pushforwardCommShift

universe u

namespace AlgebraicGeometry.Scheme.DeRham
namespace ProjectiveBundle

variable {S X P : Scheme.{u}} {E : X.Modules}
variable (f : X ⟶ S) (E : X.Modules) (r : ℕ)
variable [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
variable (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π E)

variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{u}
    (Cohomology.coefficientHom (structureSquare f π)))
  (ModuleQis.{u}
    (RingedSpace.DeRham.coefficientSite (π ≫ f).toLRSHom.toShHom))]

/- Remark 50.14.2 (1): the derived projective-bundle map defined by the powers of
`c₁ᵈᴿ(𝒪_P(1))` is an isomorphism. -/
@[stacks 0FUN] #check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.derivedMapIsIso f E r π hπ :
    IsIso (derivedMap f E r π hπ))

/- Remark 50.14.2 (2): the zeroth component of the projective-bundle map is the
canonical derived pullback `c_{P/X}`. -/
@[stacks 0FUN] #check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.derivedMap_ι_zero f E r π hπ :
    ∀ hr : 0 < r,
    biproduct.ι (fun t : Fin r ↦ (derivedComplex f)⟦-(2 * (t : ℕ) : ℤ)⟧)
        ⟨0, hr⟩ ≫ derivedMap f E r π hπ =
      ShiftedHom.sourceShiftEquiv (derivedComplex f) (derivedTarget f π) 0
        (ShiftedHom.mk₀ 0 rfl
          (Cohomology.derivedPullback (structureSquare f π))))

/- Remark 50.14.2 (3): after normalizing its recursive degree, the `t`-fold
tautological first-Chern action is the class action of `c₁ᵈᴿ(𝒪_P(1)) ^ t`. -/
@[stacks 0FUN] #check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.canonicalChernMapPower_eq_classAction f π hπ :
    ∀ t : ℕ,
    cast (congrArg (fun n : ℤ ↦ ShiftedHom (derivedComplex (π ≫ f))
      (derivedComplex (π ≫ f)) n) (chernMapDegree_eq t))
        (canonicalChernMapPower f π hπ t) =
      CanonicalAction.map (π ≫ f) (2 * (t : ℤ)) (canonicalChernPower f π hπ t))

/- Remark 50.14.2 (4): on the `t`-th summand, the derived projective-bundle map is
shifted pullback followed by the pushed action of `c₁ᵈᴿ(𝒪_P(1)) ^ t`. -/
@[stacks 0FUN] #check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.derivedMap_ι_eq f E r π hπ :
    ∀ t : Fin r,
    biproduct.ι (fun i : Fin r ↦ (derivedComplex f)⟦-(2 * (i : ℕ) : ℤ)⟧) t ≫
        derivedMap f E r π hπ =
      ShiftedHom.sourceShiftEquiv (derivedComplex f) (derivedTarget f π)
        (2 * (t : ℕ) : ℤ)
        (Cohomology.derivedPullback (structureSquare f π) ≫
          (modulePushforwardDerived.{u}
            (Cohomology.coefficientHom (structureSquare f π))).shiftedHomMap
              (Iso.refl _) (Iso.refl _) (2 * (t : ℕ) : ℤ)
                (cast (congrArg (fun n : ℤ ↦
                  ShiftedHom (derivedComplex (π ≫ f)) (derivedComplex (π ≫ f)) n)
                    (chernMapDegree_eq t)) (canonicalChernMapPower f π hπ t))))

/- Remark 50.14.2 (5): the canonical pullback together with the restriction to the
positive summands is an isomorphism. -/
@[stacks 0FUN] #check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.headTailMapIsIso f E r π hπ :
    ∀ hr : 0 < r,
    IsIso (headTailMap f E r π hπ hr))

/- Remark 50.14.2 (6): multiplication by `c₁ᵈᴿ(𝒪_P(1))` intertwines the
restrictions to `K` and `M` under the canonical identification `K ≅ M[2]`. -/
@[stacks 0FUN] #check (AlgebraicGeometry.Scheme.DeRham.ProjectiveBundle.decompositionSquare f E r π hπ :
    ∀ hr : 0 < r,
    CommSq (tailShiftIso f r).hom (initialMap f E r π hπ)
      ((shiftFunctor _ (2 : ℤ)).map (tailMap f E r π hπ))
      (canonicalPushedFirstChernMap f π hπ))

end ProjectiveBundle
end AlgebraicGeometry.Scheme.DeRham
