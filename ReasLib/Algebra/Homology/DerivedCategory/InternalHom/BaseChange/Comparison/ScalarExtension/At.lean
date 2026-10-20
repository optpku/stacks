/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.BaseChange.Comparison.At
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.CategoryTheory.Monoidal.Functor.TensorComparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Carrier-polymorphic scalar-extension facade for canonical RHom base change

This file specializes the carrier-polymorphic comparison to the canonical derived
extension-of-scalars functor.  The target module carrier has universe `max s v`, exactly as in
`ModuleCat.derivedExtensionOfScalars.{r, s, v}`.  The tensor comparison and coherent closed
comparisons remain explicit inputs. The existing derived-availability witness is retained
throughout the facade, so every comparison uses the caller's same derived functor.

@stack 08I4
-/

@[expose] public section

noncomputable section

universe r s v

open CategoryTheory

namespace CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.At

variable {R : Type r} {S : Type s} [CommRing R] [CommRing S]
variable (σ : R →+* S)
variable [hasLeftDerived : (ModuleCat.extendScalarsToDerived.{r, s, v} σ).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (ModuleCat.{v, r} R) (ComplexShape.up ℤ))]

/-- 08I4: The canonical carrier-polymorphic derived extension-of-scalars functor. -/
@[stacks 08I4 "carrier-polymorphic derived scalar-extension functor for canonical RHom"]
noncomputable abbrev functor :
    RHom.At.Derived.{r, v} (R := R) ⥤
      RHom.At.Derived.{s, max s v} (R := S) :=
  ModuleCat.derivedExtensionOfScalars.{r, s, v} σ (hasLeftDerived := hasLeftDerived)

/-- 08I4: The honest tensor-bifunctor comparison required by carrier-polymorphic scalar
extension. -/
@[stacks 08I4 "carrier-polymorphic tensor comparison input for derived scalar extension"]
noncomputable abbrev TensorComparison
    [MonoidalCategory (RHom.At.Derived.{r, v} (R := R))]
    [MonoidalCategory (RHom.At.Derived.{s, max s v} (R := S))] :=
  Functor.TensorComparison (functor σ)

/-- 08I4: The source bifunctor for carrier-polymorphic scalar-extension base change of canonical
`RHom`. -/
@[stacks 08I4 "carrier-polymorphic scalar-extension RHom base-change source"]
noncomputable abbrev sourceFunctor
    [RHom.At.Has.{r, v} (R := R)] :=
  RHom.BaseChange.At.sourceFunctor (functor σ)

/-- 08I4: The target bifunctor for carrier-polymorphic scalar-extension base change of canonical
`RHom`. -/
@[stacks 08I4 "carrier-polymorphic scalar-extension RHom base-change target"]
noncomputable abbrev targetFunctor
    [RHom.At.Has.{s, max s v} (R := S)] :=
  RHom.BaseChange.At.targetFunctor (functor σ)

section Comparison

variable [MonoidalCategory (RHom.At.Derived.{r, v} (R := R))]
variable [MonoidalCategory (RHom.At.Derived.{s, max s v} (R := S))]
variable [RHom.At.Has.{r, v} (R := R)]
variable [RHom.At.Has.{s, max s v} (R := S)]

/-- 08I4: A component of the carrier-polymorphic scalar-extension comparison for canonical
`RHom`. -/
@[stacks 08I4 "carrier-polymorphic scalar-extension RHom base-change component"]
noncomputable abbrev comparisonApp
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : TensorComparison σ)
    (K L : RHom.At.Derived.{r, v} (R := R)) :=
  RHom.BaseChange.At.comparisonApp (functor σ) M M' T K L

/-- 08I4: The coherent carrier-polymorphic scalar-extension comparison for canonical `RHom`. -/
@[stacks 08I4 "carrier-polymorphic scalar-extension RHom base-change comparison"]
noncomputable abbrev comparison
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : TensorComparison σ) :
    sourceFunctor σ ⟶ targetFunctor σ :=
  RHom.BaseChange.At.comparison (functor σ) M M' T

/-- 08I4: The carrier-polymorphic scalar-extension comparison has the explicit generic
base-change component at `(K,L)`. -/
@[simp, stacks 08I4 "carrier-polymorphic scalar-extension RHom base-change component formula"]
theorem comparison_app
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : TensorComparison σ)
    (K L : RHom.At.Derived.{r, v} (R := R)) :
    (comparison σ M M' T).app (Opposite.op K, L) = comparisonApp σ M M' T K L :=
  RHom.BaseChange.At.comparison_app (functor σ) M M' T K L

/-- 08I4: Contravariant source naturality of the carrier-polymorphic scalar-extension
comparison. -/
@[reassoc, stacks 08I4 "carrier-polymorphic scalar-extension RHom source naturality"]
theorem comparison_natural_source
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : TensorComparison σ)
    {K₁ K₂ : RHom.At.Derived.{r, v} (R := R)} (f : K₂ ⟶ K₁)
    (L : RHom.At.Derived.{r, v} (R := R)) :
    (functor σ).map (RHom.At.map (R := R) f (𝟙 L)) ≫ comparisonApp σ M M' T K₂ L =
      comparisonApp σ M M' T K₁ L ≫
        RHom.At.map (R := S) ((functor σ).map f) (𝟙 ((functor σ).obj L)) :=
  RHom.BaseChange.At.comparison_natural_source (functor σ) M M' T f L

/-- 08I4: Covariant target naturality of the carrier-polymorphic scalar-extension comparison. -/
@[reassoc, stacks 08I4 "carrier-polymorphic scalar-extension RHom target naturality"]
theorem comparison_natural_target
    (M : RHom.At.BifunctorComparison (R := R))
    (M' : RHom.At.BifunctorComparison (R := S))
    (T : TensorComparison σ)
    (K : RHom.At.Derived.{r, v} (R := R))
    {L₁ L₂ : RHom.At.Derived.{r, v} (R := R)} (f : L₁ ⟶ L₂) :
    (functor σ).map (RHom.At.map (R := R) (𝟙 K) f) ≫ comparisonApp σ M M' T K L₂ =
      comparisonApp σ M M' T K L₁ ≫
        RHom.At.map (R := S) (𝟙 ((functor σ).obj K)) ((functor σ).map f) :=
  RHom.BaseChange.At.comparison_natural_target (functor σ) M M' T K f

end Comparison

end CategoryTheory.DerivedCategory.InternalHom.RHom.BaseChange.ScalarExtension.At
