/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.OpenRestriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Open immersions of locally ringed spaces

The canonical mathlib predicate remains the owner.  This file provides its
stalkwise criterion and the universal interface for the image-open
restriction.
-/

@[expose] public section

noncomputable section

open CategoryTheory Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

/-- An open immersion is an open embedding which induces
isomorphisms on every stalk. -/
@[stacks 01HE]
theorem IsOpenImmersion.iff_isIso_stalkMap
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    IsOpenImmersion f ↔
      IsOpenEmbedding f.base ∧ ∀ x : X, IsIso (f.stalkMap x) := sorry

/-- The range of an open immersion is open. -/
@[stacks 01HE "open image of an open immersion"]
theorem IsOpenImmersion.isOpen_range
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpen (Set.range f.base) := sorry

namespace Hom

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The underlying map of an open immersion is an open embedding. -/
@[stacks 01HE "open-embedding readout"]
theorem isOpenEmbedding : IsOpenEmbedding f.base := sorry

/-- The image of an open immersion as an open subset of its target. -/
@[stacks 01HE "image open of an open immersion"]
def opensRange : Opens Y :=
  ⟨Set.range f.base, H.base_open.isOpen_range⟩

/-- Membership in the image open is witnessed by a source point. -/
@[simp, stacks 01HE "membership in the image open"]
theorem mem_opensRange {y : Y} :
    y ∈ f.opensRange ↔ ∃ x, f.base x = y := sorry

/-- The inverse image of the image open of an open immersion is the top open. -/
@[simp, stacks 01HH "preimage of the image open"]
theorem preimage_opensRange : f.preimageOpen f.opensRange = ⊤ := sorry

end Hom

namespace IsOpenImmersion

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [H : IsOpenImmersion f]

/-- The canonical inverse of a surjective open immersion, obtained from the universal property
of open immersions. -/
@[stacks 01HH "inverse of a surjective open immersion"]
noncomputable def inverseOfSurjective (hf : Function.Surjective f.base) : Y ⟶ X :=
  lift f (𝟙 Y) (fun y _ ↦ hf y)

/-- The canonical inverse of a surjective open immersion is a left inverse. -/
@[reassoc (attr := simp), stacks 01HH "surjective open immersion left inverse"]
theorem inverseOfSurjective_comp (hf : Function.Surjective f.base) :
    inverseOfSurjective f hf ≫ f = 𝟙 Y := sorry

/-- The canonical inverse of a surjective open immersion is a right inverse. -/
@[reassoc (attr := simp), stacks 01HH "surjective open immersion right inverse"]
theorem comp_inverseOfSurjective (hf : Function.Surjective f.base) :
    f ≫ inverseOfSurjective f hf = 𝟙 X := sorry

/-- A surjective open immersion, bundled as its canonical explicit isomorphism. -/
@[stacks 01HH "surjective open immersion isomorphism"]
noncomputable def isoOfSurjective (hf : Function.Surjective f.base) : X ≅ Y where
  hom := f
  inv := inverseOfSurjective f hf
  hom_inv_id := comp_inverseOfSurjective f hf
  inv_hom_id := inverseOfSurjective_comp f hf

/-- The forward map of the canonical isomorphism of a surjective open immersion is the original
open immersion. -/
@[simp, stacks 01HH "surjective open immersion isomorphism forward map"]
theorem isoOfSurjective_hom (hf : Function.Surjective f.base) :
    (isoOfSurjective f hf).hom = f := sorry

/-- The inverse map of the canonical isomorphism of a surjective open immersion is its canonical
open-immersion lift. -/
@[simp, stacks 01HH "surjective open immersion isomorphism inverse map"]
theorem isoOfSurjective_inv (hf : Function.Surjective f.base) :
    (isoOfSurjective f hf).inv = inverseOfSurjective f hf := sorry

/-- A map to the image-open restriction is canonical exactly when its
composite with the inclusion is `f`. -/
@[stacks 01HH "image-open restriction characterization"]
theorem eq_isoRestrict_hom_iff
    (g : X ⟶ Y.restrict H.base_open) :
    g = (isoRestrict f).hom ↔
      g ≫ Y.ofRestrict H.base_open = f := sorry

/-- An open immersion is uniquely isomorphic to its canonical
image-open restriction. -/
@[stacks 01HH]
theorem existsUnique_isoRestrict :
    ∃! e : X ≅ Y.restrict H.base_open,
      e.hom ≫ Y.ofRestrict H.base_open = f := sorry

end IsOpenImmersion

end AlgebraicGeometry.LocallyRingedSpace
