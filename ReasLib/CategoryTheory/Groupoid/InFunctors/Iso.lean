module

public import ReasLib.CategoryTheory.Groupoid.InFunctors

/-!
# Isomorphisms of groupoids in functors

Explicit inverse pairs of compatible morphisms and their identity isomorphisms.
-/

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- An isomorphism of groupoids in functors is a pair of inverse morphisms. -/
structure Iso (G H : GroupoidInFunctors.{u, v, w} C) where
  /-- The forward morphism. -/
  hom : Hom G H
  /-- The inverse morphism. -/
  inv : Hom H G
  /-- The two morphisms compose to the identity on the source. -/
  hom_inv_id : Hom.comp hom inv = Hom.id G
  /-- The two morphisms compose to the identity on the target. -/
  inv_hom_id : Hom.comp inv hom = Hom.id H

/-- The identity isomorphism of a groupoid in functors. -/
def Iso.refl (G : GroupoidInFunctors.{u, v, w} C) : Iso G G where
  hom := Hom.id G
  inv := Hom.id G
  hom_inv_id := Hom.id_comp (Hom.id G)
  inv_hom_id := Hom.id_comp (Hom.id G)

/-- The forward morphism of the identity isomorphism is the identity morphism. -/
theorem Iso.refl_hom (G : GroupoidInFunctors.{u, v, w} C) :
    (Iso.refl G).hom = Hom.id G := rfl

end CategoryTheory.GroupoidInFunctors
