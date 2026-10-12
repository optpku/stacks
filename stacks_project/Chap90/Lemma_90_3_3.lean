/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Factorization
import StacksCheckRecall

/-!
# Factorization into small extensions

A surjective morphism in the base category `ArtinianLocalAlgCat Λ k` factors as a
finite composition of small extensions.
-/

@[expose] public section

open CategoryTheory ComposableArrows

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.3.3: a surjective morphism `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`
can be factored as a composition of small extensions. -/
@[stacks 06GE] #check (ArtinianLocalAlgCat.exists_smallExtension_composition :
  ∀ {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    Function.Surjective f.toRingHom →
      ∃ (n : ℕ) (F : ComposableArrows (ArtinianLocalAlgCat Λ k) n)
        (e : Arrow.mk F.hom ≅ Arrow.mk f),
        ∀ i : Fin n,
          ArtinianLocalAlgCat.IsSmallExtension (F.map (homOfLE i.castSucc_le_succ)))
