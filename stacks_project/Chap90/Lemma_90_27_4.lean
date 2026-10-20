module

public import ReasLib.CategoryTheory.Groupoid.InFunctors.QuotientMap
public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Rigidity
import StacksCheckRecall

/-!
# Autoequivalences of minimal smooth prorepresentable quotients

The quotient of a minimal smooth prorepresentable groupoid in functors on `C_Λ`
does not admit autoequivalences which are not automorphisms.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.27.4: every autoequivalence over the base of the quotient of a
minimal smooth prorepresentable groupoid in functors is an isomorphism. -/
@[stacks 06KQ] #check (CategoryTheory.GroupoidInFunctors.isIso_of_isEquivalence :
  ∀ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
    [CategoryTheory.GroupoidInFunctors.IsSmooth G.s G.t] →
    [CategoryTheory.GroupoidInFunctors.IsProrepresentable G] →
    [CategoryTheory.GroupoidInFunctors.IsMinimal G] →
    ∀ (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor G.forget),
      [BasedFunctor.IsEquivalence φ] → IsIso φ)
