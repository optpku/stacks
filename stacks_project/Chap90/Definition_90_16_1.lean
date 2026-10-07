module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/- Definition 90.16.1: a category `F` cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` satisfies condition (RS) if every cospan `x₁ ⟶ x ← x₂`
in `F` lying over a cospan `A₁ ⟶ A ← A₂` in `ArtinianLocalAlgCat Λ k` with
`A₂ ⟶ A` surjective admits a fibre product `x₁ ×_x x₂` in `F` whose square lies
over the ring-level fibre product `A₁ ×_A A₂`. This is owned by
`Functor.HasRimSchlessinger`. -/
@[stacks 06J2]
#check (Functor.HasRimSchlessinger p : Prop)
