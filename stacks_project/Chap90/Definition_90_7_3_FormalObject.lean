module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject

/-! Compatibility checks for formal objects and their morphisms. -/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

#check (FormalObject.of_base :
  ∀ (R : CompleteLocalAlgCat Λ k) (ξ : ℕ → F) (f : ∀ n, ξ (n + 1) ⟶ ξ n)
    (over_obj : ∀ n, p.obj (ξ n) = R.truncation n)
    (over_step : ∀ n, p.IsHomLift (R.truncationMap n) (f n)),
    (FormalObject.of R ξ f over_obj over_step).base = R)

#check (FormalObject.Hom.comp_app :
  ∀ {ξ η ζ : FormalObject p} (a : ξ ⟶ η) (b : η ⟶ ζ) (n : ℕ),
    (FormalObject.Hom.comp a b).app n = a.app n ≫ b.app n)

