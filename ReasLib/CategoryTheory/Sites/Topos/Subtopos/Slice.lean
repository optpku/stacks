/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Subterminal
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Basic

/-!
# Slice presentations and open subtopoi

The comparison between a presented topos and a slice topos is concrete data.
`PresentsSlice` is its proposition-level existence form.  This keeps a chosen
equivalence out of ordinary assumptions while giving constructions that need
it a precise data owner.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

namespace MorphismOfTopoiIn

/-- Concrete data exhibiting a morphism of topoi as the slice topos at a
sheaf `U`. -/
structure SlicePresentation
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K) (U : Sheaf J (Type w)) where
  /-- The equivalence from the source sheaf topos to the slice at `U`. -/
  equivalence : Sheaf K (Type w) ≌ Over U
  /-- Under this equivalence, inverse image is the canonical slice functor. -/
  inverseImageIso : f.inverseImage ⋙ equivalence.functor ≅ Over.star U

/-- A morphism of topoi presents the slice at `U` when it admits a concrete
`SlicePresentation`. -/
def PresentsSlice
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K) (U : Sheaf J (Type w)) : Prop :=
  Nonempty (SlicePresentation f U)

/-- The source-semantic existence form of a slice presentation. -/
theorem PresentsSlice.spec
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, w} J K} {U : Sheaf J (Type w)}
    (h : f.PresentsSlice U) :
    ∃ e : Sheaf K (Type w) ≌ Over U, Nonempty (f.inverseImage ⋙ e.functor ≅ Over.star U) := sorry

end MorphismOfTopoiIn

namespace GrothendieckTopology

/-- Concrete data presenting an open subtopos by a subterminal slice.  The
underlying subtopos presentation owns the presenting site and morphism, so
the slice-specific data does not duplicate them or constrain their universes. -/
structure OpenSubtoposPresentation
    {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) (P : ObjectProperty (Sheaf J (Type w))) where
  /-- The subterminal sheaf defining the slice. -/
  U : Sheaf J (Type w)
  /-- The defining sheaf is subterminal. -/
  isSubterminal : IsSubterminal U
  /-- The site presentation of the underlying subtopos. -/
  toSubtoposPresentation : SubtoposPresentation.{u₁, u₂, v₁, v₂, w} J P
  /-- The source topos is concretely identified with the slice at `U`. -/
  slicePresentation :
    @MorphismOfTopoiIn.SlicePresentation C _ toSubtoposPresentation.D
      toSubtoposPresentation.categoryD J toSubtoposPresentation.K
      toSubtoposPresentation.morphism U

/-- The concrete slice data of an open-subtopos presentation yields the
corresponding proposition-level slice condition. -/
theorem OpenSubtoposPresentation.presentsSlice
    {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {P : ObjectProperty (Sheaf J (Type w))}
    (presentation : OpenSubtoposPresentation.{u₁, u₂, v₁, v₂, w} J P) :
    @MorphismOfTopoiIn.PresentsSlice C _ presentation.toSubtoposPresentation.D
      presentation.toSubtoposPresentation.categoryD J presentation.toSubtoposPresentation.K
      presentation.toSubtoposPresentation.morphism presentation.U := sorry

/-- Definition 7.43.4: an open subtopos is the essential image of the direct
image of a site presentation of the slice at a subterminal sheaf. -/
@[stacks 08LX]
def IsOpenSubtopos
    {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    (P : ObjectProperty (Sheaf J (Type w))) : Prop :=
  Nonempty (OpenSubtoposPresentation.{u₁, u₂, v₁, v₂, w} J P)

/-- The carrier of an open subtopos is a subtopos. -/
theorem IsOpenSubtopos.isSubtopos
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {P : ObjectProperty (Sheaf J (Type w))}
    (hP : IsOpenSubtopos.{u₁, u₂, v₁, v₂, w} P) :
    IsSubtopos.{u₁, u₂, v₁, v₂, w} J P := sorry

end GrothendieckTopology

end CategoryTheory
