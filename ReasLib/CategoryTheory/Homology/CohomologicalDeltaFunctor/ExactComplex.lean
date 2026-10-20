/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Delta functors from exact cochain-complex functors

An exact additive functor into nonnegatively indexed cochain complexes has a canonical
cohomological delta functor. The connecting maps are the boundary maps of the image short exact
sequence. This file isolates that construction from all geometric applications.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.ComposableArrows

noncomputable section

universe vA vB uA uB

namespace CategoryTheory.CohomologicalDeltaFunctor.ExactComplex

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (K : A ⥤ CochainComplex B ℕ) [K.Additive]
variable (hK : exactFunctor A (CochainComplex B ℕ) K)

/-- The additive degree-`n` homology functor of an exact cochain-complex functor. -/
noncomputable abbrev degree (n : ℕ) : A ⥤+ B :=
  AdditiveFunctor.of
    (K ⋙ HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n)

section Exact

include hK

/-- An exact cochain-complex functor sends a short exact sequence to a short exact sequence of
complexes. -/
theorem map_shortExact {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map K).ShortExact := sorry

/-- The connecting morphism in homology of the image of a short exact sequence. -/
@[stacks 01EK "connecting morphism of an exact cochain-complex functor"]
noncomputable def connecting {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    ((degree K n).obj).obj S.X₃ ⟶ ((degree K (n + 1)).obj).obj S.X₁ :=
  (map_shortExact K hK hS).δ n (n + 1)
    (ComplexShape.up_mk n (n + 1) rfl)

/-- The degree-zero image of the first map of a short exact sequence is monic. -/
theorem mono_map_f_zero {S : ShortComplex A} (hS : S.ShortExact) :
    Mono ((degree K 0).obj.map S.f) := sorry

/-- The degree-zero homology branch of an exact nonnegative cochain-complex functor is left
exact. -/
theorem degree_zero_preservesFiniteLimits :
    PreservesFiniteLimits (degree K 0).obj := sorry

/-- The five-arrow homology window of an exact cochain-complex functor is exact. -/
theorem exact₅ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (mk₅ ((degree K n).obj.map S.f) ((degree K n).obj.map S.g)
      (connecting K hK hS n) ((degree K (n + 1)).obj.map S.f)
      ((degree K (n + 1)).obj.map S.g)).Exact := sorry

/-- The homology connecting morphisms are natural in morphisms of short exact sequences. -/
theorem connecting_naturality {S T : ShortComplex A}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ) :
    CommSq ((degree K n).obj.map f.τ₃) (connecting K hK hS n)
      (connecting K hK hT n) ((degree K (n + 1)).obj.map f.τ₁) := sorry

end Exact

/-- The cohomological delta functor canonically attached to an exact additive functor into
nonnegative cochain complexes. -/
@[stacks 01EK "delta functor of an exact cochain-complex functor"]
noncomputable def functor
    (K : A ⥤ CochainComplex B ℕ) [K.Additive]
    (hK : exactFunctor A (CochainComplex B ℕ) K) :
    CohomologicalDeltaFunctor A B where
  F := degree K
  δ := fun {S} hS n ↦ connecting K hK (S := S) hS n
  mono_map_f_zero := fun {S} hS ↦ mono_map_f_zero K hK (S := S) hS
  exact₅ := fun {S} hS n ↦ exact₅ K hK (S := S) hS n
  δ_naturality := fun {S T} hS hT f n ↦
    connecting_naturality K hK (S := S) (T := T) hS hT f n

/-- The cohomological delta functor attached to a bundled exact cochain-complex functor. -/
@[stacks 01EK "delta functor from a bundled exact cochain-complex functor"]
noncomputable def functorBundled
    (K : ExactFunctor A (CochainComplex B ℕ)) :
    CohomologicalDeltaFunctor A B :=
  functor K.1 K.2

/-- The cohomological delta functor attached to an ordinary cochain-complex functor together with
its exactness proof.  Additivity is inferred from exactness. -/
@[stacks 01EK "delta functor from exactness of a cochain-complex functor"]
noncomputable def functorOfExact
    (K : CategoryTheory.Functor A (CochainComplex B ℕ))
    (hK : exactFunctor A (CochainComplex B ℕ) K) :
    CohomologicalDeltaFunctor A B :=
  functorBundled ⟨K, hK⟩

/-- The degree branches of the delta functor attached to a bundled exact cochain-complex
functor. -/
@[simp, stacks 01EK "degree formula for a bundled exact cochain-complex functor"]
theorem functorBundled_obj
    (K : ExactFunctor A (CochainComplex B ℕ)) (n : ℕ) :
    ((functorBundled K).F n).obj = K.1 ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n := sorry

/-- The connecting morphism attached to a bundled exact cochain-complex functor. -/
@[simp, stacks 01EK "connecting formula for a bundled exact cochain-complex functor"]
theorem functorBundled_δ
    (K : ExactFunctor A (CochainComplex B ℕ))
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (functorBundled K).δ hS n = connecting K.1 K.2 hS n := sorry

/-- The degree branches of `functor K hK` are the homology functors of `K`. -/
@[simp]
theorem functor_obj (n : ℕ) :
    ((functor K hK).F n).obj = K ⋙
      HomologicalComplex.homologyFunctor B (ComplexShape.up ℕ) n := sorry

/-- The connecting morphism of `functor K hK` is the boundary map of the mapped short exact
sequence. -/
@[simp]
theorem functor_δ {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (functor K hK).δ hS n = connecting K hK hS n := sorry

end CategoryTheory.CohomologicalDeltaFunctor.ExactComplex
