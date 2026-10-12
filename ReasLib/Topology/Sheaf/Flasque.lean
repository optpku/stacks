/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Flasque sheaves: extensions of Mathlib's API

This module extends Mathlib's `IsFlasque` with additional results needed for sheaf cohomology
computations in the Stacks Project formalization.

## Main declarations

- `TopCat.Sheaf.Flasque.restriction_surjective_type`: restriction maps are surjective
- `TopCat.Sheaf.Flasque.pushforward_isFlasque`: pushforward preserves flasqueness
- `TopCat.Sheaf.Flasque.globalSections_surjective_of_epi`: exactness on global sections

## References

- [Stacks Project, Tag 01EK](https://stacks.math.columbia.edu/tag/01EK)
- [Hartshorne, Algebraic Geometry, II.2]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

noncomputable section

universe w v u

namespace TopCat.Sheaf.Flasque

variable {X : TopCat.{w}}

/-- A flasque sheaf has surjective restriction maps (for `Type`-valued sheaves). -/
theorem restriction_surjective_type
    (F : TopCat.Sheaf (Type v) X) [IsFlasque F]
    {U V : Opens X} (hUV : U ≤ V) :
    Function.Surjective (F.presheaf.map (homOfLE hUV).op) := sorry

/-- Pushforward of a flasque sheaf along a continuous map is flasque. -/
theorem pushforward_isFlasque {C : Type u} [Category.{v} C]
    {Y : TopCat.{w}} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) [IsFlasque F] :
    IsFlasque ((TopCat.Sheaf.pushforward C f).obj F) := sorry

/-- The global sections functor sends epimorphisms from a flasque sheaf to surjective maps
on global sections. This is the key exactness property. -/
theorem globalSections_surjective_of_epi
    (F G : TopCat.Sheaf (Type v) X) [IsFlasque F]
    (η : F ⟶ G) (hη : Epi η) :
    Function.Surjective (η.hom.app (op ⊤)) := sorry

/-- Every injective object in the sheaf category is flasque. -/
theorem of_injective
    (I : TopCat.Sheaf (Type v) X) [Injective I] :
    IsFlasque I := sorry

/-- A short exact sequence with flasque first two terms has flasque third term.
The exactness hypothesis states that `f` is the kernel of `g` on each open. -/
theorem of_shortExact_of_flasque
    (F G H : TopCat.Sheaf (Type v) X)
    [IsFlasque F] [IsFlasque G]
    (f : F ⟶ G) (g : G ⟶ H)
    (hf : Mono f) (hg : Epi g)
    (hex : ∀ (U : Opens X) (s : G.presheaf.obj (op U)),
      (∀ x, g.hom.app (op U) s = g.hom.app (op U) x → s = x) ∨
        s ∈ Set.range (f.hom.app (op U))) :
    IsFlasque H := sorry

end TopCat.Sheaf.Flasque

end

end
