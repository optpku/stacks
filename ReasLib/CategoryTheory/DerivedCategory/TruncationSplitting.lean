/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import ReasLib.CategoryTheory.DerivedCategory.Ext

@[expose] public section

/-!
# Splitting Bounded Derived Objects by Cohomology

This module owns the intrinsic family of shifted cohomology objects of a derived object and the
finite-biproduct decompositions obtained when higher extension groups between distinct
cohomological degrees vanish.  The bounded interval is part of the realization theorem, not of
the underlying family.
-/

universe w' w v u

namespace DerivedCategory

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedExt

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w'} 𝒜] [HasExt.{w} 𝒜]

namespace ShiftedCohomology

/-- Stacks 0GM4: the intrinsic degree-indexed family `i ↦ H⁽i⁾(K)[-i]` associated to a derived
object. -/
@[stacks 0GM4]
noncomputable abbrev family (K : DerivedCategory 𝒜) :
    ℤ → DerivedCategory 𝒜 :=
  fun i ↦ (singleFunctor 𝒜 i).obj ((homologyFunctor 𝒜 i).obj K)

/-- Stacks 0GM4: the restriction of `family` to the finite integer interval `[a, b]`.
-/
@[stacks 0GM4]
noncomputable abbrev on (K : DerivedCategory 𝒜) (a b : ℤ) :
    Finset.Icc a b → DerivedCategory 𝒜 :=
  fun i ↦ family 𝒜 K i

namespace Split

/-- Under higher-Ext vanishing, the upper truncation of an object bounded below by `a` splits as
the finite biproduct of its shifted cohomology objects through degree `a + n`. -/
@[stacks 0GM4]
theorem truncLE
    (K : DerivedCategory 𝒜) (a : ℤ) (hGE : K.IsGE a)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((homologyFunctor 𝒜 i).obj K) ((homologyFunctor 𝒜 j).obj K) n)) :
    ∀ n : ℕ,
      Nonempty (((t.truncLE (a + (n : ℤ))).obj K) ≅
        ⨁ on 𝒜 K a (a + (n : ℤ))) := sorry

/-- Stacks 0GM4: a derived object with cohomology in `[a, b]` splits into its shifted
cohomology objects over that interval when all higher extensions from a higher degree to a lower
degree vanish. -/
@[stacks 0GM4]
theorem ofBounds
    (K : DerivedCategory 𝒜) (a b : ℤ) (hGE : K.IsGE a) (hLE : K.IsLE b)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((homologyFunctor 𝒜 i).obj K) ((homologyFunctor 𝒜 j).obj K) n)) :
    Nonempty (K ≅ ⨁ on 𝒜 K a b) := sorry

/-- Stacks 0GM4: a bounded derived object splits into a finite biproduct of its shifted
cohomology objects under the higher-Ext vanishing condition. -/
@[stacks 0GM4]
theorem bounded
    (K : DerivedCategory.Bounded 𝒜)
    (hExt : ∀ (n : ℕ) (_ : 2 ≤ n) (i j : ℤ) (_ : j < i),
      Subsingleton (Ext ((homologyFunctor 𝒜 i).obj K.obj)
        ((homologyFunctor 𝒜 j).obj K.obj) n)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ on 𝒜 K.obj a b) := sorry

/-- Stacks 0EWX: uniform vanishing of degree-two Ext groups gives the bounded splitting without
requiring callers to reconstruct the higher-Ext hypothesis.

The `[EnoughProjectives 𝒜]` hypothesis is the derived-`Ext` bridge that supplies the dimension
shifting used to pass from degree two to all higher degrees. -/
@[stacks 0EWX]
theorem ofExtTwo
    [EnoughProjectives 𝒜]
    (K : DerivedCategory.Bounded 𝒜)
    (hExt₂ : ∀ A B : 𝒜, Subsingleton (Ext B A 2)) :
    ∃ a b : ℤ, Nonempty (K.obj ≅ ⨁ on 𝒜 K.obj a b) := sorry

end Split

end ShiftedCohomology

end DerivedCategory
