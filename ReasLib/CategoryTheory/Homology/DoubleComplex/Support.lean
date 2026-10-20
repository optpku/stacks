/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import ReasLib.Algebra.Homology.HomologicalComplex.DoubleComplex.Functor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support Conditions for Double Complexes

This narrow leaf records support predicates which depend only on the objects of a double complex.
It deliberately does not import total complexes, filtrations, or spectral sequences.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

universe u v

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The nonzero horizontal indices on the antidiagonal of total degree `n`. -/
@[stacks 0132 "antidiagonal support of a double complex"]
def antidiagonalSupport (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (n : ℤ) : Set ℤ :=
  {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}

/-- Every antidiagonal of a cohomological double complex has finite nonzero support. -/
@[stacks 0132 "finite antidiagonal support of a double complex"]
def AntidiagonalSupport.Finite (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) : Prop :=
  ∀ n : ℤ, (K.antidiagonalSupport n).Finite

namespace AntidiagonalSupport.Finite

variable {D : Type*} [Category D] [HasZeroMorphisms D]

/-- Applying a zero-morphism-preserving functor termwise to a double complex preserves finite
antidiagonal support.

This is the cohomological facade of `Total.Support.Finite.map`.
-/
@[stacks 0132 "functoriality of finite antidiagonal support"]
theorem map {K : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (hfin : AntidiagonalSupport.Finite K) (F : C ⥤ D) [F.PreservesZeroMorphisms] :
    AntidiagonalSupport.Finite
      ((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj K) := sorry

/-- Swapping the two indices of a double complex preserves finite antidiagonal support. -/
@[stacks 0132 "flip of finite antidiagonal support"]
theorem flip {K : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (hfin : AntidiagonalSupport.Finite K) : AntidiagonalSupport.Finite K.flip := sorry

/-- Finite antidiagonal support is invariant under swapping the two indices. -/
@[stacks 0132 "flip invariance of finite antidiagonal support"]
theorem flip_iff (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
    AntidiagonalSupport.Finite K.flip ↔ AntidiagonalSupport.Finite K := sorry

end AntidiagonalSupport.Finite

end HomologicalComplex₂
