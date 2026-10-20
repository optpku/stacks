module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Tor.Uniformity
import StacksCheckRecall

@[expose] public section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

open Abelian

/- Remark 51.21.8: if `A` is local and has finite Krull dimension `d`, then the
conclusion of Proposition 51.21.7 holds with degree bound `d` in place of the bound `t`
on the number of generators of `I`. Whether `d` can instead be replaced by the
local-cohomological dimension of `I` is left as an open question. -/
@[stacks 0GA4] #check
  (CategoryTheory.DerivedCategory.IdealPower.uniformArtinRees_of_ringKrullDim :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] → [IsLocalRing A] →
    (I : Ideal A) → (t d : ℕ) →
    (∃ a : Fin t → I,
      I = Ideal.span (Set.range fun j ↦ (a j : A))) →
    ringKrullDim A = d →
    ∃ N c : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (P : ProjectiveResolution (Ideal.PowerQuotient.stage I (ModuleCat.of A A) n))
        (P' : ProjectiveResolution
          (Ideal.PowerQuotient.stage I (ModuleCat.of A A) (n - c))),
      let α := ModuleCat.ofHom (AdicCompletion.transitionMap I A (Nat.sub_le n c))
      let c₁ := ∃ a : P.Hom P' α, ∀ i : ℕ, d < i → a.hom.f i = 0
      let c₂ := ∃ a : P.Hom P' α, a.hom.f (d + 1) = 0
      let c₃ := ∀ (M : ModuleCat.{u} A) (i : ℕ), d < i →
        (Ext.mk₀.{u} α).precomp M (zero_add i) = 0
      let c₄ := ∀ M : ModuleCat.{u} A,
        (Ext.mk₀.{u} α).precomp M (zero_add (d + 1)) = 0
      let c₅ := (Ext.mk₀.{u} α).comp
        (P'.resolutionImageExtClass.{u} d) (zero_add (d + 1)) = 0
      let c₆ := ∀ (M : ModuleCat.{u} A) (i : ℕ), d < i →
        ((Tor (ModuleCat.{u} A) i).map α).app M = 0
      let c₇ := ∀ M : ModuleCat.{u} A,
        ((Tor (ModuleCat.{u} A) (d + 1)).map α).app M = 0
      List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆, c₇] ∧ c₇)

end CategoryTheory.DerivedCategory.IdealPower
