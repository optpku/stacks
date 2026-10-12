/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Induced
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-fibre products of stacks in groupoids

The data of a two-fibre product is owned by the generic
`CategoryTheory.TwoFibreProduct` construction for the full subbicategory of categories fibred
in groupoids. This file adds exactly the stack-closure theorem needed to package that explicit
apex as a `StackOver.Groupoids`, then lifts its projections, comparison cell, and bilimit cone
through the full subbicategory of stack objects.

## Main declarations

* `CategoryTheory.StackOver.Groupoids.TwoFibreProduct.apex` — the canonical stack-valued apex.
* `CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone` — its pseudopullback cone.
* `CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone.isBilimit` — the bilimit property.
* `CategoryTheory.StackOver.Groupoids.hasPseudoPullbacks` — pseudopullbacks in the stack
  bicategory.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y S :
  StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J}

namespace StackOver.Groupoids

namespace TwoFibreProduct

/-- The groupoid-fibered two-fibre-product owner underlying a cospan of stacks. This reducible
view pins the generic full-subbicategory apex to `FiberedCategoryOver.Groupoids C`; all
non-`Prop` data remain owned by `CategoryTheory.TwoFibreProduct.apex`. -/
@[stacks 02ZL "groupoid-stack two-fibre-product ambient carrier"]
abbrev ambient
    (F : X ⟶ S) (G : Y ⟶ S) : FiberedCategoryOver.Groupoids C :=
  CategoryTheory.TwoFibreProduct.apex.{u, v, w, vB} F.hom G.hom

/-- The generic groupoid-fibred two-fibre-product apex of a cospan of stacks is a stack on the
site. This is the only additional closure input beyond the reusable
`CategoryTheory.TwoFibreProduct` data construction. -/
@[stacks 02ZL "groupoid-stack two-fibre-product closure"]
theorem isStackOnSite
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsStack.OnSite J (ambient F G).p := sorry

/-- The canonical two-fibre product of two morphisms of stacks in groupoids. Its non-`Prop`
data are owned by `CategoryTheory.TwoFibreProduct.apex`; the second field records precisely the
stack closure theorem above. -/
@[stacks 02ZL "groupoid-stack two-fibre-product apex"]
noncomputable abbrev apex
    (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Groupoids J :=
  ObjectProperty.FullSubbicategory.mk _ (ambient F G) (isStackOnSite F G)

/-- Forgetting the stack witness from the groupoid-valued apex recovers the neutral
groupoid-fibred two-fibre product. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product ambient readout"]
theorem apex.toGroupoids (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).toGroupoids = ambient F G := sorry

/-- The left projection from the canonical two-fibre product of stacks in groupoids. -/
@[stacks 02ZL "groupoid-stack two-fibre-product first projection"]
noncomputable abbrev fst
    (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ⟶ X :=
  Bicategory.InducedBicategory.mkHom
    (CategoryTheory.TwoFibreProduct.fst.{u, v, w, vB} F.hom G.hom)

/-- Forgetting the stack condition from the left projection recovers the neutral
groupoid-fibred projection. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product first projection readout"]
theorem fst.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (fst F G).hom =
      CategoryTheory.TwoFibreProduct.fst.{u, v, w, vB} F.hom G.hom := sorry

/-- The right projection from the canonical two-fibre product of stacks in groupoids. -/
@[stacks 02ZL "groupoid-stack two-fibre-product second projection"]
noncomputable abbrev snd
    (F : X ⟶ S) (G : Y ⟶ S) :
    apex F G ⟶ Y :=
  Bicategory.InducedBicategory.mkHom
    (CategoryTheory.TwoFibreProduct.snd.{u, v, w, vB} F.hom G.hom)

/-- Forgetting the stack condition from the right projection recovers the neutral
groupoid-fibred projection. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product second projection readout"]
theorem snd.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (snd F G).hom =
      CategoryTheory.TwoFibreProduct.snd.{u, v, w, vB} F.hom G.hom := sorry

/-- The canonical comparison isomorphism between the two projection composites
of the groupoid-valued stack two-fibre product. -/
@[stacks 02ZL "groupoid-stack two-fibre-product comparison"]
noncomputable abbrev comparisonIso
    (F : X ⟶ S) (G : Y ⟶ S) :
    fst F G ≫ F ≅ snd F G ≫ G :=
  Bicategory.InducedBicategory.isoMk
    (CategoryTheory.TwoFibreProduct.comparisonIso.{u, v, w, vB}
      F.hom G.hom)

/-- Forgetting the forward stack-level comparison cell recovers the neutral
groupoid-fibred comparison cell. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product comparison forward readout"]
theorem comparisonIso.hom (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).hom.hom =
      (CategoryTheory.TwoFibreProduct.comparisonIso.{u, v, w, vB}
        F.hom G.hom).hom := sorry

/-- Forgetting the inverse stack-level comparison cell recovers the inverse neutral
groupoid-fibred comparison cell. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product comparison inverse readout"]
theorem comparisonIso.inv (F : X ⟶ S) (G : Y ⟶ S) :
    (comparisonIso F G).inv.hom =
      (CategoryTheory.TwoFibreProduct.comparisonIso.{u, v, w, vB}
        F.hom G.hom).inv := sorry

/-- The canonical pseudopullback cone of stacks in groupoids. Its comparison isomorphism is the
generic groupoid-fibred comparison cell, lifted through the full stack subbicategory. -/
@[stacks 02ZL "groupoid-stack two-fibre-product cone"]
noncomputable abbrev cone
    (F : X ⟶ S) (G : Y ⟶ S) :
    Bicategory.PseudoPullbackCone F G :=
  Bicategory.PseudoPullbackCone.inFull
    (IsStack.InGroupoids.objectProperty J)
    (CategoryTheory.TwoFibreProduct.cone.{u, v, w, vB} F.hom G.hom)
    (isStackOnSite F G)

/-- The apex of the canonical groupoid-valued stack cone is the explicit
two-fibre product. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product cone apex readout"]
theorem cone.pt (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).pt = apex F G := sorry

/-- The first leg of the canonical groupoid-valued stack cone is its first
projection. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product cone first leg readout"]
theorem cone.fst (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).fst = fst F G := sorry

/-- The second leg of the canonical groupoid-valued stack cone is its second
projection. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product cone second leg readout"]
theorem cone.snd (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).snd = snd F G := sorry

/-- The structural cell of the canonical groupoid-valued stack cone is its
comparison isomorphism. -/
@[simp, stacks 02ZL "groupoid-stack two-fibre-product cone comparison readout"]
theorem cone.iso (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).iso = comparisonIso F G := sorry

namespace cone

/-- The canonical cone is a bilimit of the walking cospan in the bicategory of stacks in
groupoids over `(C, J)`. -/
@[stacks 02ZL "bilimit cone for a two-fibre product of stacks in groupoids", instance]
theorem isBilimit
    (F : X ⟶ S) (G : Y ⟶ S) :
    (CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone F G).IsBilimit := sorry

end cone

/- The reported `sorryAx` is inherited through the full-subbicategory membership proof and
upstream category/bicategory law fields. The carrier, projections, and comparison data are the
explicit `BasedCategory.PseudoPullback` constructions exposed above. -/

end TwoFibreProduct

/-- The bicategory of stacks in groupoids over a site has pseudopullbacks. -/
@[stacks 02ZL "pseudopullbacks of stacks in groupoids"]
instance hasPseudoPullbacks : Bicategory.HasPseudoPullbacks (StackOver.Groupoids J) := sorry

end StackOver.Groupoids

end CategoryTheory
