module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (M : C) (d₀ d₁ : M ⟶ M)
variable (hd₀d₁ : d₀ ≫ d₁ = 0) (hd₁d₀ : d₁ ≫ d₀ = 0)

/- 12.11.2.1 [02MW]: two endomorphisms with zero composites determine the canonical
`ZMod 2`-indexed cochain complex with constant object `M` and alternating differentials. -/
@[stacks 02MW]
#check (((⟨M, d₀, d₁, hd₀d₁, hd₁d₀⟩ : TwoPeriodicEndomorphism C).toCochainComplex) :
  CochainComplex C (ZMod 2))

/- The reusable owner exposes both degree objects and both differentials directly. -/
#check ((⟨M, d₀, d₁, hd₀d₁, hd₁d₀⟩ : TwoPeriodicEndomorphism C).toCochainComplex_X)
#check ((⟨M, d₀, d₁, hd₀d₁, hd₁d₀⟩ : TwoPeriodicEndomorphism C).toCochainComplex_d_zero)
#check ((⟨M, d₀, d₁, hd₀d₁, hd₁d₀⟩ : TwoPeriodicEndomorphism C).toCochainComplex_d_one)

end CategoryTheory
