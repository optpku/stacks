module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger

/-!
# Rim-Schlessinger condition (RS)

A category cofibered in groupoids over `C_Λ` satisfies (RS) when every cospan in the
total category lying over a cospan `A₁ → A ← A₂` in `C_Λ` with `A₂ → A` surjective
admits a fibre product whose image is a fibre product in `C_Λ`.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

#check (CategoryTheory.Functor.HasRimSchlessinger p : Prop)

#check (CategoryTheory.Functor.hasRimSchlessinger_spec p :
  CategoryTheory.Functor.HasRimSchlessinger p ↔
    CategoryTheory.Functor.IsFibered.InGroupoids p.op ∧
      ∀ {x x1 x2 : F} (f1 : x1 ⟶ x) (f2 : x2 ⟶ x),
        Function.Surjective (p.map f2).hom →
          ∃ (w : F) (π1 : w ⟶ x1) (π2 : w ⟶ x2),
            IsPullback π1 π2 f1 f2 ∧
              IsPullback (p.map π1) (p.map π2) (p.map f1) (p.map f2))
