module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import ReasLib.RingTheory.RingHom.SmallExtension
public import stacks_project.Chap90.Definition_90_7_3_ArtinianLocal

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

namespace ArtinianLocalAlgCat

/-- Lemma 90.3.3: a surjective morphism `f : B ⟶ A` in `ArtinianLocalAlgCat Λ k`
can be factored as a composition of small extensions. -/
@[stacks 06GE]
theorem exists_smallExtension_composition
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.hom) :
    ∃ (n : ℕ) (F : ComposableArrows (ArtinianLocalAlgCat Λ k) n)
      (e : Arrow.mk F.hom ≅ Arrow.mk f),
      ∀ i : Fin n,
        (F.map (homOfLE i.castSucc_le_succ)).hom.toRingHom.IsSmallExtension :=
  sorry

end ArtinianLocalAlgCat
