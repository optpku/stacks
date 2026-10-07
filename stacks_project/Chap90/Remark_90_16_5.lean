module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Remark_90_16_5_SchlessingerH4

/-!
# Rim-Schlessinger versus Schlessinger's (H4)

When a category cofibered over `ArtinianLocalAlgCat Λ k` is cofibered in sets,
hence associated to a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`, the
Rim-Schlessinger condition (RS) is Schlessinger's condition (H4).
-/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Remark 90.16.5: when a category cofibered over `ArtinianLocalAlgCat Λ k` is
cofibered in sets, associated to a functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v`,
the Rim-Schlessinger condition (RS) is exactly Schlessinger's condition (H4). -/
@[stacks 06J6]
theorem hasRimSchlessinger_iff_hasSchlessingerH4
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    HasRimSchlessinger (CategoryOfElements.π F) ↔ HasSchlessingerH4 F := sorry

end CategoryTheory.Functor
