/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.Data.Fin.Rev
public import ReasLib.AlgebraicGeometry.ChernClass.Theory

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v w x

namespace AlgebraicGeometry.ChernClass

/-- The data relevant to the projective-bundle construction of the Chern classes of a
constant-rank finite locally free module.  The equivalence is the projective-bundle formula,
written using cup product in the cohomology ring and pullback along `p`.
This legacy type is retained for existing source-facing consumers. New code should derive it
using `CohomologyTheory.projectiveBundleContext`; it stores no equivalence/formula cache. -/
structure ProjectiveBundleContext
    {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
    (A : Cᵒᵖ ⥤ RingCat.{x}) (X P : C) (E : (toScheme.obj X).Modules) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (p : P ⟶ X)
    (hP : Scheme.ProjectiveBundle.Representation (toScheme.map p) E) where
  /-- The first Chern class of an invertible module. -/
  firstChernClass :
    ∀ (Y : C) (L : (toScheme.obj Y).Modules),
      Scheme.Modules.Invertible L → A.obj (Opposite.op Y)
  /-- Bijectivity of the explicit projective-bundle formula; no equivalence cache is stored. -/
  projectiveBundleMap_bijective : Function.Bijective fun a : Fin r → A.obj (Opposite.op X) ↦
    ∑ i : Fin r,
      firstChernClass P
            (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
            (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) ^ i.1 *
        A.map p.op (a i)

namespace ProjectiveBundleContext

variable {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
  (A : Cᵒᵖ ⥤ RingCat.{x}) (X P : C) (E : (toScheme.obj X).Modules) (r : ℕ)
  [Scheme.Modules.IsFiniteLocallyFreeOfRank r E] (p : P ⟶ X)
  (hP : Scheme.ProjectiveBundle.Representation (toScheme.map p) E)

variable (S : ProjectiveBundleContext toScheme A X P E r p hP)

section DerivedEquivalence

variable {toScheme A X P E r p hP}

/-- The equivalence derived from the supplied bijectivity of the displayed formula. -/
def projectiveBundleEquiv :
    (Fin r → A.obj (Opposite.op X)) ≃ A.obj (Opposite.op P) :=
  Equiv.ofBijective (fun a ↦
    ∑ i : Fin r,
      S.firstChernClass P
            (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
            (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) ^ i.1 *
        A.map p.op (a i)) S.projectiveBundleMap_bijective

/-- The derived equivalence has the specified projective-bundle formula. -/
theorem projectiveBundleEquiv_apply (a : Fin r → A.obj (Opposite.op X)) :
    S.projectiveBundleEquiv a =
      ∑ i : Fin r,
        S.firstChernClass P
              (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
              (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) ^ i.1 *
          A.map p.op (a i) := rfl

end DerivedEquivalence

/-- The class `c₁(𝒪_P(1))` of the tautological invertible module on the projective
bundle. -/
def tautologicalFirstChernClass : A.obj (Opposite.op P) :=
  S.firstChernClass P
    (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
    (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP)

/-- The tautological first Chern class is obtained by applying the context's first Chern
class operation to `𝒪_P(1)`. -/
theorem tautologicalFirstChernClass_def :
    S.tautologicalFirstChernClass =
      S.firstChernClass P
        (Scheme.ProjectiveBundle.tautologicalSheaf (toScheme.map p) hP)
        (Scheme.ProjectiveBundle.tautologicalSheaf_isInvertible (toScheme.map p) hP) := rfl

/-- The signed projective-bundle coordinates of the negative top power of
`c₁(𝒪_P(1))`. -/
def signedChernCoordinates : Fin r → A.obj (Opposite.op X) :=
  S.projectiveBundleEquiv.symm
    (-((-1 : A.obj (Opposite.op P)) ^ r * S.tautologicalFirstChernClass ^ r))

/-- Applying the projective-bundle equivalence to the signed Chern coordinates gives the
negative top power of `c₁(𝒪_P(1))`. -/
theorem projectiveBundleEquiv_signedChernCoordinates :
    S.projectiveBundleEquiv S.signedChernCoordinates =
      -((-1 : A.obj (Opposite.op P)) ^ r * S.tautologicalFirstChernClass ^ r) :=
  S.projectiveBundleEquiv.apply_symm_apply _

/-- The Chern classes `c^A_j(E)` determined by the projective-bundle formula, with
`c^A_0(E) = 1`. -/
def chernClass : Fin (r + 1) → A.obj (Opposite.op X) :=
  Fin.cons 1 fun (j : Fin r) ↦
    (-1 : A.obj (Opposite.op X)) ^ (Fin.rev j).1 *
      signedChernCoordinates toScheme A X P E r p hP S (Fin.rev j)

/-- The degree-zero Chern class determined by the projective-bundle formula is `1`. -/
theorem chernClass_zero :
    chernClass toScheme A X P E r p hP S 0 = 1 := rfl

/-- The alternating projective-bundle relation for the Chern classes determined by the context. -/
theorem chernClass_relation :
    ∑ i : Fin (r + 1),
      (-1 : A.obj (Opposite.op P)) ^ i.1 *
        S.tautologicalFirstChernClass ^ i.1 *
          A.map p.op
            (chernClass toScheme A X P E r p hP S (Fin.rev i)) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.rev_last, chernClass_zero, map_one, mul_one, Fin.val_last]
  have hsum :
      (∑ i : Fin r,
        (-1 : A.obj (Opposite.op P)) ^ i.castSucc.1 *
          S.tautologicalFirstChernClass ^ i.castSucc.1 *
            A.map p.op
              (chernClass toScheme A X P E r p hP S (Fin.rev i.castSucc))) =
        S.projectiveBundleEquiv S.signedChernCoordinates := by
    rw [S.projectiveBundleEquiv_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Fin.rev_castSucc, chernClass, Fin.cons_succ, Fin.rev_rev,
      map_mul, map_pow, map_neg, map_one, Fin.val_castSucc]
    rcases neg_one_pow_eq_or (A.obj (Opposite.op P)) i.1 with h | h <;>
      simp [h, tautologicalFirstChernClass]
  rw [hsum, projectiveBundleEquiv_signedChernCoordinates]
  exact neg_add_cancel _

end ProjectiveBundleContext

namespace CohomologyTheory

/-- Derive the legacy projective-bundle adapter from a theory's geometric model and axiom (4). -/
def projectiveBundleContext
    {C : Type u} [Category.{v} C] {toScheme : C ⥤ Scheme.{w}}
    {A : Cᵒᵖ ⥤ RingCat.{x}}
    {Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))}
    [∀ X, GradedAlgebra (Agrade X)] (S : CohomologyTheory toScheme A Agrade)
    (X : C)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty (toScheme.obj X).Modules))
    (r : ℕ) (h_E : Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj) :
    @ProjectiveBundleContext C _ toScheme A X (S.projectiveBundle X E) E.obj r h_E
      (S.projectiveBundleProjection X E) (S.projectiveBundleRepresentation X E) where
  firstChernClass Y L hL :=
    S.firstChernClass Y (@Scheme.Modules.picardClass (toScheme.obj Y) L hL)
  projectiveBundleMap_bijective := S.projectiveBundleMap_bijective X E r h_E

end CohomologyTheory

end AlgebraicGeometry.ChernClass
