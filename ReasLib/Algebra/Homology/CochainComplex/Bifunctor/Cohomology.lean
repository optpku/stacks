/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.PointwiseBifunctor
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MC

# Cohomology products for heterogeneous coefficient bifunctors

This is the bifunctor-level core of the cup-product boundary formalism.  The coefficient
operation is an explicit `T : A ⥤ B ⥤ D`; in particular, a module tensor product may have input
categories in different universes.  The concrete cocycle map is exposed first, while its chain
compatibility and descent laws remain proposition-valued statements.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex

noncomputable section

universe uA vA uB vB uD vD

namespace HomologicalComplex.CohomologyCup.Bifunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable {T : A ⥤ B ⥤ D}
variable [T.PreservesZeroMorphisms] [∀ X, (T.obj X).PreservesZeroMorphisms]
variable {K : CochainComplex A ℤ} {L : CochainComplex B ℤ} {H : CochainComplex D ℤ}
variable [HomologicalComplex.HasMapBifunctor K L T (up ℤ)]

/-! ### Cocycles and induced cohomology maps -/

/-- The concrete map on two cocycles associated to a heterogeneous chain pairing. -/
@[stacks 07MC "heterogeneous chain pairing on cocycles"]
noncomputable abbrev cocycleMap
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H) (p q : ℤ) :
    (T.obj (K.cycles p)).obj (L.cycles q) ⟶ H.X (p + q) :=
  (T.map (K.iCycles p)).app (L.cycles q) ≫
    (T.obj (K.X p)).map (L.iCycles q) ≫
    HomologicalComplex.ιMapBifunctor K L T (up ℤ) p q (p + q) rfl ≫ γ.f (p + q)

/-- The cocycle part of the boundary-cup construction: a heterogeneous chain pairing sends two
cocycles to a cocycle in the target complex. -/
@[stacks 07MC "heterogeneous chain pairing sends cocycles to cocycles"]
theorem cocycleMap_d
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H) (p q : ℤ) :
    cocycleMap γ p q ≫ H.d (p + q) (p + q + 1) = 0 := sorry

/-- The cohomology morphism obtained by evaluating a heterogeneous chain pairing on cocycles. -/
@[stacks 07MC "heterogeneous cohomology pairing on cycles"]
noncomputable def cycles
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H) (p q : ℤ) :
    (T.obj (K.cycles p)).obj (L.cycles q) ⟶ H.homology (p + q) :=
  H.liftCycles (cocycleMap γ p q) (p + q + 1) (CochainComplex.next ℤ (p + q))
    (cocycleMap_d γ p q) ≫ H.homologyπ (p + q)

/-- Transport `cycles` to a displayed target degree; the equality `h` is explicit data. -/
@[stacks 07MC "heterogeneous cohomology pairing in a displayed degree"]
noncomputable def cyclesTo
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H)
    (p q r : ℤ) (h : p + q = r) :
    (T.obj (K.cycles p)).obj (L.cycles q) ⟶ H.homology r :=
  match r, h with
  | _, rfl => cycles γ p q

/-- A heterogeneous cohomology morphism is induced by the chain pairing after the two canonical
cocycle quotient maps. -/
@[stacks 07MC "heterogeneous induced cohomology pairing"]
def IsInduced
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H) (p q : ℤ)
    (cup : (T.obj (K.homology p)).obj (L.homology q) ⟶ H.homology (p + q)) : Prop :=
  ((T.map (K.homologyπ p)).app (L.cycles q) ≫
      (T.obj (K.homology p)).map (L.homologyπ q)) ≫ cup = cycles γ p q

/-- Displayed-degree form of `IsInduced`, retaining the source-facing degree equality. -/
@[stacks 07MC "heterogeneous induced cohomology pairing in a displayed degree"]
def IsInducedTo
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H)
    (p q r : ℤ) (h : p + q = r)
    (cup : (T.obj (K.homology p)).obj (L.homology q) ⟶ H.homology r) : Prop :=
  ((T.map (K.homologyπ p)).app (L.cycles q) ≫
      (T.obj (K.homology p)).map (L.homologyπ q)) ≫ cup = cyclesTo γ p q r h

/-- In the intrinsic target degree, displayed-degree induction is ordinary induction. -/
@[stacks 07MC "intrinsic degree bridge for heterogeneous induced pairings"]
theorem isInducedTo_rfl
    (γ : HomologicalComplex.mapBifunctor K L T (up ℤ) ⟶ H) (p q : ℤ)
    (cup : (T.obj (K.homology p)).obj (L.homology q) ⟶ H.homology (p + q)) :
    IsInducedTo γ p q (p + q) rfl cup ↔ IsInduced γ p q cup := sorry

/-! ### Boundary compatibility -/

variable {SF : ShortComplex (CochainComplex A ℤ)} {SG : ShortComplex (CochainComplex B ℤ)}
variable [HomologicalComplex.HasMapBifunctor SF.X₁ SG.X₂ T (up ℤ)]
variable [HomologicalComplex.HasMapBifunctor SF.X₁ SG.X₃ T (up ℤ)]
variable [HomologicalComplex.HasMapBifunctor SF.X₂ SG.X₁ T (up ℤ)]
variable [HomologicalComplex.HasMapBifunctor SF.X₂ SG.X₂ T (up ℤ)]
variable [HomologicalComplex.HasMapBifunctor SF.X₃ SG.X₁ T (up ℤ)]

/-- Lemma 20.25.4 (07MC), heterogeneous core: compatible pairings of two short exact cochain
sequences satisfy the signed boundary-cup identity. The displayed `Epi` hypothesis applies to
the bifunctor image of the canonical cocycle pullback covers followed by the homology quotients.
Only this local descent map must be epi; no global additivity or epi-preservation is required. -/
@[stacks 07MC "heterogeneous boundary-cup compatibility"]
theorem boundary
    (hF : SF.ShortExact) (hG : SG.ShortExact)
    (γ₁ : HomologicalComplex.mapBifunctor SF.X₁ SG.X₃ T (up ℤ) ⟶ H)
    (γ₂ : HomologicalComplex.mapBifunctor SF.X₂ SG.X₂ T (up ℤ) ⟶ H)
    (γ₃ : HomologicalComplex.mapBifunctor SF.X₃ SG.X₁ T (up ℤ) ⟶ H)
    (hγ₁ : CommSq
      (HomologicalComplex.mapBifunctorMap (𝟙 SF.X₁) SG.g T (up ℤ))
      (HomologicalComplex.mapBifunctorMap SF.f (𝟙 SG.X₂) T (up ℤ)) γ₁ γ₂)
    (hγ₃ : CommSq
      (HomologicalComplex.mapBifunctorMap SF.g (𝟙 SG.X₁) T (up ℤ))
      (HomologicalComplex.mapBifunctorMap (𝟙 SF.X₂) SG.f T (up ℤ)) γ₃ γ₂)
    (n m : ℤ)
    [Epi ((T.map (pullback.snd (SF.g.f n) (SF.X₃.iCycles n) ≫
        SF.X₃.homologyπ n)).app (pullback (SG.g.f m) (SG.X₃.iCycles m)) ≫
      (T.obj (SF.X₃.homology n)).map
        (pullback.snd (SG.g.f m) (SG.X₃.iCycles m) ≫ SG.X₃.homologyπ m))]
    (cup₁ : (T.obj (SF.X₁.homology (n + 1))).obj (SG.X₃.homology m) ⟶
      H.homology (n + m + 1))
    (cup₃ : (T.obj (SF.X₃.homology n)).obj (SG.X₁.homology (m + 1)) ⟶
      H.homology (n + m + 1))
    (hcup₁ : IsInducedTo γ₁ (n + 1) m (n + m + 1) (add_right_comm n 1 m) cup₁)
    (hcup₃ : IsInducedTo γ₃ n (m + 1) (n + m + 1) (add_assoc n m 1).symm cup₃) :
    (T.map (hF.δ n (n + 1) rfl)).app (SG.X₃.homology m) ≫ cup₁ =
      (n + 1).negOnePow •
        ((T.obj (SF.X₃.homology n)).map (hG.δ m (m + 1) rfl) ≫ cup₃) := sorry

end HomologicalComplex.CohomologyCup.Bifunctor

end
