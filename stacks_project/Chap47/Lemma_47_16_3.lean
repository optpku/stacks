/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteLength
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 47.16.3: Every `A`-linear self-equivalence of the category of finite-length
modules over a Noetherian local commutative ring `A` is naturally isomorphic to the identity. -/
@[stacks 0A7P] #check
  (ModuleCat.finiteLengthSelfEquivalenceIsoId :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (F : (Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).FullSubcategory ⥤
        (Module.FiniteLengthDeterminant.moduleProperty.{u, u} A).FullSubcategory),
      [Functor.Linear A F] → [F.IsEquivalence] → Nonempty (F ≅ 𝟭 _))
