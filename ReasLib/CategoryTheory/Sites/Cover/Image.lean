module

public import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.Tactic.CrossRefAttribute

/-!
# Images of cover arrow families

This leaf records the form in which a continuous functor sends a chosen
Grothendieck cover to a covering family.  The statement deliberately uses the
canonical `Sieve.ofArrows` presentation rather than introducing a second
bundled image-cover object.
-/

@[expose] public section

universe uC uD vC vD

namespace CategoryTheory.GrothendieckTopology.Cover

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable {U : C}

/-- The image arrows of a cover under a continuous functor generate a covering sieve. -/
theorem imageArrows_mem
    (T : J.Cover U) (u : C ⥤ D) [u.IsContinuous J K] :
    Sieve.ofArrows (fun I : T.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) ∈ K (u.obj U) := sorry

end CategoryTheory.GrothendieckTopology.Cover
