/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.Additive
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Antidiagonal
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalHomotopy.Flip
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Degreewise split short complexes of double complexes

Degreewise splittings in either direction assemble on antidiagonals to splittings of the short
complex of total complexes.  The induced connecting maps agree with totalization and the
corresponding total-shift comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex

noncomputable section

universe v u

namespace HomologicalComplex₂.DegreewiseSplit

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCountableCoproducts C]
variable (S : ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)))

/-- The short complex obtained by applying coproduct totalization. -/
abbrev totalShortComplex : ShortComplex (CochainComplex C ℤ) :=
  S.map (totalFunctor C (up ℤ) (up ℤ) (up ℤ))

section FirstDirection

variable (σ : ∀ p : ℤ, (S.map (eval (CochainComplex C ℤ) (up ℤ) p)).Splitting)

/-- The antidiagonal retraction assembled from splittings in the first direction. -/
noncomputable def retraction₁ (n : ℤ) :
    (S.X₂.total (up ℤ)).X n ⟶ (S.X₁.total (up ℤ)).X n :=
  antidiagonalMap (fun p q ↦ ((σ p).r).f q) n

/-- The antidiagonal section assembled from splittings in the first direction. -/
noncomputable def section₁ (n : ℤ) :
    (S.X₃.total (up ℤ)).X n ⟶ (S.X₂.total (up ℤ)).X n :=
  antidiagonalMap (fun p q ↦ ((σ p).s).f q) n

/-- The first-direction antidiagonal retraction retracts the totalized first map. -/
theorem f_retraction₁ (n : ℤ) :
    (total.map S.f (up ℤ)).f n ≫ retraction₁ S σ n = 𝟙 _ := sorry

/-- The first-direction antidiagonal section sections the totalized second map. -/
theorem section₁_g (n : ℤ) :
    section₁ S σ n ≫ (total.map S.g (up ℤ)).f n = 𝟙 _ := sorry

/-- The first-direction antidiagonal retraction and section satisfy the splitting identity. -/
theorem retraction₁_f_add_g_section₁ (n : ℤ) :
    retraction₁ S σ n ≫ (total.map S.f (up ℤ)).f n +
        (total.map S.g (up ℤ)).f n ≫ section₁ S σ n =
      𝟙 _ := sorry

/-- Splittings in the first direction induce a degreewise splitting after totalization. -/
@[stacks 0G6B]
noncomputable def splitting₁ (n : ℤ) :
    ((totalShortComplex S).map (eval C (up ℤ) n)).Splitting where
  r := retraction₁ S σ n
  s := section₁ S σ n
  f_r := f_retraction₁ S σ n
  s_g := section₁_g S σ n
  id := retraction₁_f_add_g_section₁ S σ n

/-- Totalizing the first-direction connecting map gives the connecting map of the totalized
degreewise splitting. -/
@[stacks 0G6B]
theorem connectingHom_total₁ :
    total.map (CochainComplex.homOfDegreewiseSplit S σ) (up ℤ) ≫
        (S.X₁.totalShift₁Iso 1).hom =
      CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (splitting₁ S σ) := sorry

end FirstDirection

section SecondDirection

variable (σ : ∀ q : ℤ,
  (S.map ((flipFunctor C (up ℤ) (up ℤ)) ⋙
    eval (CochainComplex C ℤ) (up ℤ) q)).Splitting)

/-- The antidiagonal retraction assembled from splittings in the second direction. -/
noncomputable def retraction₂ (n : ℤ) :
    (S.X₂.total (up ℤ)).X n ⟶ (S.X₁.total (up ℤ)).X n :=
  antidiagonalMap (fun p q ↦ ((σ q).r).f p) n

/-- The antidiagonal section assembled from splittings in the second direction. -/
noncomputable def section₂ (n : ℤ) :
    (S.X₃.total (up ℤ)).X n ⟶ (S.X₂.total (up ℤ)).X n :=
  antidiagonalMap (fun p q ↦ ((σ q).s).f p) n

/-- The second-direction antidiagonal retraction retracts the totalized first map. -/
theorem f_retraction₂ (n : ℤ) :
    (total.map S.f (up ℤ)).f n ≫ retraction₂ S σ n = 𝟙 _ := sorry

/-- The second-direction antidiagonal section sections the totalized second map. -/
theorem section₂_g (n : ℤ) :
    section₂ S σ n ≫ (total.map S.g (up ℤ)).f n = 𝟙 _ := sorry

/-- The second-direction antidiagonal retraction and section satisfy the splitting identity. -/
theorem retraction₂_f_add_g_section₂ (n : ℤ) :
    retraction₂ S σ n ≫ (total.map S.f (up ℤ)).f n +
        (total.map S.g (up ℤ)).f n ≫ section₂ S σ n =
      𝟙 _ := sorry

/-- Splittings in the second direction induce a degreewise splitting after totalization. -/
@[stacks 0G6A]
noncomputable def splitting₂ (n : ℤ) :
    ((totalShortComplex S).map (eval C (up ℤ) n)).Splitting where
  r := retraction₂ S σ n
  s := section₂ S σ n
  f_r := f_retraction₂ S σ n
  s_g := section₂_g S σ n
  id := retraction₂_f_add_g_section₂ S σ n

/-- The connecting map obtained from the degreewise splitting in the second direction. -/
@[stacks 0G6A]
noncomputable def connectingHom₂ : S.X₃ ⟶ S.X₁.bidegreeShift 0 1 :=
  HomologicalComplex₂.Total.Homotopy.Second.fromFlipToShift 1
    (CochainComplex.homOfDegreewiseSplit
      (S.map (flipFunctor C (up ℤ) (up ℤ))) σ)

/-- Totalizing the second-direction connecting map gives the connecting map of the totalized
degreewise splitting, including the second-direction Koszul comparison. -/
@[stacks 0G6A]
theorem connectingHom_total₂ :
    total.map (connectingHom₂ S σ) (up ℤ) ≫
        (BidegreeShift.totalIso S.X₁ 0 1).hom =
      CochainComplex.homOfDegreewiseSplit (totalShortComplex S) (splitting₂ S σ) := sorry

end SecondDirection

end HomologicalComplex₂.DegreewiseSplit
