module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Properties
public import stacks_project.Chap50.Proposition_50_19_3

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

set_option synthInstance.checkSynthOrder false in
/-- The relative Frobenius of a smooth morphism of fixed relative dimension in prime
characteristic is finite. -/
instance relativeFrobenius_isFinite_of_smooth {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    IsFinite (relativeFrobenius (p := p) f) := sorry

set_option synthInstance.checkSynthOrder false in
/-- The relative Frobenius of a smooth morphism of fixed relative dimension in prime
characteristic is syntomic. -/
instance relativeFrobenius_syntomic_of_smooth {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (f : X ⟶ S)
    [SmoothOfRelativeDimension d f] :
    Syntomic (relativeFrobenius (p := p) f) := sorry

/-- The relative Frobenius and its target structure morphism form the canonical square over
the base scheme. -/
theorem relativeFrobenius_overCommSq {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (f : X ⟶ S) :
    CommSq (relativeFrobenius (p := p) f) f
      (relativeFrobeniusTargetOver (p := p) f).hom (𝟙 S) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule

/-- The relative de Rham trace for the relative Frobenius, using a specified valid trace
rule. -/
noncomputable def relativeFrobeniusTrace {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [IsFinite (Scheme.Hom.relativeFrobenius (p := p) f)]
    [Syntomic (Scheme.Hom.relativeFrobenius (p := p) f)] :=
  relativeComplexMap r hr (Scheme.Hom.relativeFrobenius (p := p) f) f
    (Scheme.Hom.relativeFrobeniusTargetOver (p := p) f).hom
    (Scheme.Hom.relativeFrobenius_overCommSq (p := p) f)

/-- The degree-`i` component of the relative-Frobenius trace is the corresponding relative
trace component. -/
theorem relativeFrobeniusTrace_f {p : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [IsFinite (Scheme.Hom.relativeFrobenius (p := p) f)]
    [Syntomic (Scheme.Hom.relativeFrobenius (p := p) f)] (i : ℕ) :
    (relativeFrobeniusTrace (p := p) r hr f).f i =
      relativeComponent r hr (Scheme.Hom.relativeFrobenius (p := p) f) f
        (Scheme.Hom.relativeFrobeniusTargetOver (p := p) f).hom
        (Scheme.Hom.relativeFrobenius_overCommSq (p := p) f) i := sorry

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
    (relativeFrobeniusTrace (p := p) r hr f).f i = 0 := sorry

/-- In the relative dimension, the relative-Frobenius trace component is an epimorphism. -/
instance relativeFrobeniusTrace_epi {p d : ℕ} [Fact p.Prime]
    {X S : Scheme.{u}} [Scheme.IsCharP S p] (r : TraceRule.{u}) (hr : IsTraceRule r)
    (f : X ⟶ S) [SmoothOfRelativeDimension d f] :
    Epi ((relativeFrobeniusTrace (p := p) r hr f).f d) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule
