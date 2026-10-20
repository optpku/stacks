module

public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.FrobeniusTrace
import StacksCheckRecall

/- Lemma 50.19.5 (1): the relative Frobenius of a smooth morphism of fixed
relative dimension in prime characteristic is finite. -/
@[stacks 0FW2] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_isFinite_of_smooth :
    ∀ {p d : ℕ} [Fact p.Prime]
      {X S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.Scheme.IsCharP S p]
      (f : X ⟶ S) [AlgebraicGeometry.SmoothOfRelativeDimension d f],
      AlgebraicGeometry.IsFinite
        (AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) f))

/- Lemma 50.19.5 (2): the relative Frobenius of a smooth morphism of fixed
relative dimension in prime characteristic is syntomic. -/
@[stacks 0FW2] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_syntomic_of_smooth :
    ∀ {p d : ℕ} [Fact p.Prime]
      {X S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.Scheme.IsCharP S p]
      (f : X ⟶ S) [AlgebraicGeometry.SmoothOfRelativeDimension d f],
      AlgebraicGeometry.Syntomic
        (AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) f))

/- Lemma 50.19.5 (3): the relative de Rham trace of the relative Frobenius vanishes in
every degree different from the relative dimension. -/
@[stacks 0FW2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeFrobeniusTrace_eq_zero :
    ∀ {p d : ℕ} [Fact p.Prime]
      {X S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.Scheme.IsCharP S p]
      (r : AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule)
      (hr : AlgebraicGeometry.Scheme.RelativeDifferentials.IsTraceRule r)
      (f : X ⟶ S) [AlgebraicGeometry.SmoothOfRelativeDimension d f]
      (i : ℕ) (_ : i ≠ d),
      (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeFrobeniusTraceOfSmooth
        d (p := p) r hr f).f i = 0)

/- Lemma 50.19.5 (4): the relative de Rham trace of the relative Frobenius is an
epimorphism in the relative dimension. -/
@[stacks 0FW2] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeFrobeniusTrace_epi :
    ∀ {p d : ℕ} [Fact p.Prime]
      {X S : AlgebraicGeometry.Scheme} [AlgebraicGeometry.Scheme.IsCharP S p]
      (r : AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule)
      (hr : AlgebraicGeometry.Scheme.RelativeDifferentials.IsTraceRule r)
      (f : X ⟶ S) [AlgebraicGeometry.SmoothOfRelativeDimension d f],
      CategoryTheory.Epi
        ((AlgebraicGeometry.Scheme.RelativeDifferentials.TraceRule.relativeFrobeniusTraceOfSmooth
          d (p := p) r hr f).f d))

