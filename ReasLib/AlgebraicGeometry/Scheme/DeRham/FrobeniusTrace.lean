/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Trace

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

namespace TraceRule

/-- The relative de Rham trace for relative Frobenius, using a specified valid trace rule. -/
noncomputable def relativeFrobeniusTrace {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [IsFinite (Scheme.Hom.relativeFrobenius (p := p) f)]
    [Syntomic (Scheme.Hom.relativeFrobenius (p := p) f)] :=
  relativeComplexMap r hr (Scheme.Hom.relativeFrobenius (p := p) f) f
    (Scheme.Hom.relativeFrobeniusTargetOver (p := p) f).hom
    (CommSq.mk (Scheme.Hom.relativeFrobenius_snd (p := p) f))

/-- The relative de Rham trace for the relative Frobenius of a smooth morphism of fixed
relative dimension in prime characteristic, using a specified valid trace rule. -/
noncomputable def relativeFrobeniusTraceOfSmooth (d : ℕ) {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] :=
  @relativeFrobeniusTrace p ‹Fact p.Prime› X S ‹Scheme.IsCharP S p› r hr f
    (Scheme.Hom.relativeFrobenius_isFinite_of_smooth (p := p) (d := d) f)
    (Scheme.Hom.relativeFrobenius_syntomic_of_smooth (p := p) (d := d) f)

/-- The relative-Frobenius trace is independent of the specified valid trace rule. -/
theorem relativeFrobeniusTrace_eq {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p]
    (r₁ : TraceRule.{u}) (hr₁ : IsTraceRule r₁)
    (r₂ : TraceRule.{u}) (hr₂ : IsTraceRule r₂) (f : X ⟶ S)
    [IsFinite (Scheme.Hom.relativeFrobenius (p := p) f)]
    [Syntomic (Scheme.Hom.relativeFrobenius (p := p) f)] :
    relativeFrobeniusTrace (p := p) r₁ hr₁ f =
      relativeFrobeniusTrace (p := p) r₂ hr₂ f := sorry

/-- Away from the relative dimension, the relative-Frobenius trace component vanishes. -/
theorem relativeFrobeniusTrace_eq_zero {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] (i : ℕ) (hi : i ≠ d) :
    (relativeFrobeniusTraceOfSmooth d (p := p) r hr f).f i = 0 := sorry

/-- In the relative dimension, the relative-Frobenius trace component is an epimorphism. -/
theorem relativeFrobeniusTrace_epi {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] :
    Epi ((relativeFrobeniusTraceOfSmooth d (p := p) r hr f).f d) := sorry

end TraceRule

end AlgebraicGeometry.Scheme.RelativeDifferentials
