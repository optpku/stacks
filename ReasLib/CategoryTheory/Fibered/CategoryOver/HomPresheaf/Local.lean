module

public import Mathlib.CategoryTheory.Sites.Localization
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf
public import ReasLib.CategoryTheory.Fibered.CategoryOver.HomPresheaf.LocallySurjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local properties of Hom-presheaf maps

This module specializes the isomorphism-invariant API for canonical
Hom-presheaf maps to the local equivalences of a Grothendieck topology.
-/

@[expose] public section

universe u v uS vS

namespace CategoryTheory

namespace FiberedCategoryOver.Hom

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, uS, vS} C}

/-- Membership in the local-equivalence class of the slice site is invariant
under isomorphism of the owning morphisms of fibered categories. -/
theorem presheafHomMap.ownerIso.mem_W_iff
    (J : GrothendieckTopology C) {F G : X ⟶ Y} (e : F ≅ G)
    {U : C} (x y : X.p.Fiber U) :
    (J.over U).W (presheafHomMap F x y) ↔
      (J.over U).W (presheafHomMap G x y) := sorry

end FiberedCategoryOver.Hom

end CategoryTheory
