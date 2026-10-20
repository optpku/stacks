/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.StrongTrans.Construction
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso

/-!
# Computations for locally induced transformations to the identity

This leaf exposes the component and naturality data of toId, including semantic ambient readouts
that do not depend on the full-subcategory representation.
-/

@[expose] public section

namespace CategoryTheory.Bicategory.LocallyInducedBicategory

open CategoryTheory ObjectProperty
open scoped CategoryTheory.Bicategory

universe w v u uB

variable {B : Type uB}
variable {D : Type u} [Bicategory.{w, v} D]
variable {F : B → D} {Q : HomProperty F} [Q.IsMultiplicative]

namespace StrongTrans

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

variable (G : StrictPseudofunctor (LocallyInducedBicategory D F Q)
  (InducedBicategory D F))
variable (map_mem : ∀ {X Y : LocallyInducedBicategory D F Q} (f : X ⟶ Y),
  Q (G.obj X) (G.obj Y) (G.map f).hom)
variable (η : Pseudofunctor.StrongTrans G.toPseudofunctor
  (ι D F Q).toPseudofunctor)
variable (app_mem : ∀ X : LocallyInducedBicategory D F Q,
  Q (G.obj X) X (η.app X).hom)

/-- A toId component is the original ambient component bundled with its hom-property witness. -/
@[simp]
theorem toId.app (X : LocallyInducedBicategory D F Q) :
    (toId G map_mem η app_mem).app X =
      mkHom (η.app X).hom (app_mem X) := sorry

/-- The ambient representative of a toId component is the original ambient component. -/
@[simp]
theorem toId.app.toAmbient (X : LocallyInducedBicategory D F Q) :
    ((toId G map_mem η app_mem).app X).obj = (η.app X).hom := sorry

/-- Naturality of toId is the original ambient naturality isomorphism bundled by the hom
property. -/
@[simp]
theorem toId.naturality {X Y : LocallyInducedBicategory D F Q} (f : X ⟶ Y) :
    (toId G map_mem η app_mem).naturality f =
      (Q _ _).isoMk (InducedBicategory.Iso.toAmbient (η.naturality f)) := sorry

/-- The ambient forward cell of toId naturality is the original forward naturality cell. -/
@[simp]
theorem toId.naturality.hom.toAmbient
    {X Y : LocallyInducedBicategory D F Q} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((toId G map_mem η app_mem).naturality f)).hom =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).hom := sorry

/-- The ambient inverse cell of toId naturality is the original inverse naturality cell. -/
@[simp]
theorem toId.naturality.inv.toAmbient
    {X Y : LocallyInducedBicategory D F Q} (f : X ⟶ Y) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((toId G map_mem η app_mem).naturality f)).inv =
      (InducedBicategory.Iso.toAmbient (η.naturality f)).inv := sorry

end StrongTrans

end CategoryTheory.Bicategory.LocallyInducedBicategory
