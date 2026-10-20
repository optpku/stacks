module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmallExtension

/-!
# Factorization into small extensions

Surjective morphisms of residue-identified Artinian local algebras factor into
finitely many small extensions.
-/

@[expose] public section

open CategoryTheory ComposableArrows

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- Every surjective morphism of residue-identified Artinian local algebras is
isomorphic to a finite composition of small extensions. -/
theorem exists_smallExtension_composition
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (hf : Function.Surjective f.toRingHom) :
    ∃ (n : ℕ) (F : ComposableArrows (ArtinianLocalAlgCat Λ k) n)
      (e : Arrow.mk F.hom ≅ Arrow.mk f),
      ∀ i : Fin n, IsSmallExtension (F.map (homOfLE i.castSucc_le_succ)) := sorry

end ArtinianLocalAlgCat
