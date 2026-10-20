module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.Algebra.Homology.DerivedCategory.Ext.Functor
public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective-amplitude splittings from derived Ext

@stack 0A5P
@stack 0G97
@stack 0G98

This leaf owns the two truncation-splitting criteria obtained from the functor
`DerivedCategory.Ext.addCommGrpFunctor`.  The first assumes preservation of monomorphisms; the
second specializes to a zero Ext functor and removes the degree-`a` cohomology summand.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.ProjectiveAmplitude

open DerivedCategory.TStructure

variable {R : Type u} [Ring R]

/-- Lemma 15.77.5: if `Ext^{-a}_R(K, -)` preserves monomorphisms, then the upper truncation of
`K` has projective amplitude in `[a + 1, b]` for some `b`, and the canonical truncation triangle
has a unique compatible biproduct splitting. -/
@[stacks 0G97 "Ext mono-preservation and truncation splitting"]
theorem existsUnique_truncationBiprod_of_ext_preservesMonomorphisms
    (K : DerivedCategory.Minus (ModuleCat R)) (a : ℤ)
    (hExt : (Ext.addCommGrpFunctor K.obj (-a)).PreservesMonomorphisms) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE a).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι a).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := sorry

/-- Lemma 15.77.6: if `Ext^{-a}_R(K, -)` is the zero functor, then the upper truncation has
projective amplitude in `[a + 1, b]` for some `b`, and `K` has a unique compatible splitting with
lower term `τ≤ a - 1` and upper term `τ≥ a + 1`. -/
@[stacks 0G98 "Ext vanishing and gap truncation splitting"]
theorem existsUnique_truncationGapBiprod_of_ext_isZero
    (K : DerivedCategory.Minus (ModuleCat R)) (a : ℤ)
    (hExt : IsZero (Ext.addCommGrpFunctor K.obj (-a))) :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE (a - 1)).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι (a - 1)).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj) := sorry

end CategoryTheory.DerivedCategory.ProjectiveAmplitude

namespace CategoryTheory

open scoped DerivedExt

variable {R : Type u} [Ring R]

/-- Lemma 15.69.2: projective amplitude in `[a, b]` is equivalent to the three standard
cohomology and derived-Ext vanishing criteria. -/
@[stacks 0A5P "projective amplitude and derived Ext vanishing"]
theorem projectiveAmplitudeIn_ext_vanishing_tfae
    (K : DerivedCategory (ModuleCat R)) (a b : ℤ) :
    List.TFAE
      [ HasProjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext⁽i⁾(K, (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N), e = 0
      , (∀ n : ℤ, b < n →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj K)) ∧
          ∀ (N : ModuleCat R) (i : ℤ), -a < i →
            ∀ e : Ext⁽i⁾(K, (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N), e = 0
      , (∀ n : ℤ, n ∉ Set.Icc (a - 1) b →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj K)) ∧
          ∀ (N : ModuleCat R),
            ∀ e : Ext⁽(-a + 1)⁾(K,
              (DerivedCategory.singleFunctor (ModuleCat R) 0).obj N), e = 0
      ] := sorry

end CategoryTheory
