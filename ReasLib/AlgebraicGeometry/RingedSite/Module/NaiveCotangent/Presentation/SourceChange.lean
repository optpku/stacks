module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Changing the source of a naive cotangent complex

An isomorphism between the source ring sheaves of two maps into the same target induces an
explicit isomorphism between their canonical naive cotangent complexes.  Both directions are
built from morphisms of canonical polynomial presentations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace SheafOfModules.RingedSite.NaiveCotangent.Presentation

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {A A' B : Sheaf J CommRingCat.{u}}

/-- The map between canonical presenting algebras induced by an isomorphism of base sheaves. -/
noncomputable def sourceMiddle (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B) :
    FreeAlgebra.Presentation.underlying A (Under.mk a) ⟶
      FreeAlgebra.Presentation.underlying A' (Under.mk a') :=
  (FreeAlgebra.evaluation
    (Under.mk (e.hom ≫ FreeAlgebra.Presentation.base A' (Under.mk a')))
    (FreeAlgebra.Presentation.generators (Under.mk a))
    (FreeAlgebra.Presentation.generator A' (Under.mk a'))).right

/-- The base square for changing the source of a canonical presentation. -/
theorem sourceMiddle_baseSq (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B) :
    CommSq e.hom (FreeAlgebra.Presentation.base A (Under.mk a))
      (FreeAlgebra.Presentation.base A' (Under.mk a')) (sourceMiddle e a a') := sorry

/-- The target square for changing the source of a canonical presentation. -/
theorem sourceMiddle_targetSq (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    CommSq (sourceMiddle e a a') (FreeAlgebra.Presentation.map A (Under.mk a))
      (FreeAlgebra.Presentation.map A' (Under.mk a')) (𝟙 B) := sorry

/-- The morphism of canonical presentations induced by a source isomorphism. -/
@[stacks 08TY "source change of canonical presentations"]
noncomputable def sourceHom (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    Hom (FreeAlgebra.Presentation.base A (Under.mk a))
      (FreeAlgebra.Presentation.map A (Under.mk a))
      (FreeAlgebra.Presentation.base A' (Under.mk a'))
      (FreeAlgebra.Presentation.map A' (Under.mk a')) where
  base := e.hom
  middle := sourceMiddle e a a'
  target := 𝟙 B
  baseSq := sourceMiddle_baseSq e a a'
  targetSq := sourceMiddle_targetSq e a a' h

/-- The cochain map induced by changing the source through an isomorphism. -/
@[stacks 08TY "source change map"]
noncomputable def sourceMap (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    NaiveCotangent.obj A (Under.mk a) ⟶ NaiveCotangent.obj A' (Under.mk a') :=
  (extendComplexIdIso B).inv.app (NaiveCotangent.obj A (Under.mk a)) ≫
    Hom.map (sourceHom e a a' h)

/-- The reverse source triangle commutes. -/
theorem source_inv_fac (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    a' = e.inv ≫ a := sorry

/-- Changing source along an isomorphism and then along its inverse is the identity. -/
theorem sourceMap_comp_inverse (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    sourceMap e a a' h ≫
      sourceMap e.symm a' a (source_inv_fac e a a' h) =
      𝟙 (NaiveCotangent.obj A (Under.mk a)) := sorry

/-- Changing source along the inverse isomorphism and then along the original is the identity. -/
theorem sourceMap_inverse_comp (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    sourceMap e.symm a' a (source_inv_fac e a a' h) ≫
        sourceMap e a a' h =
      𝟙 (NaiveCotangent.obj A' (Under.mk a')) := sorry

/-- Changing the source by an isomorphism does not change the canonical naive cotangent complex. -/
@[stacks 08TY "source change for naive cotangent complexes"]
noncomputable def sourceIso (e : A ≅ A') (a : A ⟶ B) (a' : A' ⟶ B)
    (h : a = e.hom ≫ a') :
    NaiveCotangent.obj A (Under.mk a) ≅ NaiveCotangent.obj A' (Under.mk a') where
  hom := sourceMap e a a' h
  inv := sourceMap e.symm a' a (source_inv_fac e a a' h)
  hom_inv_id := sourceMap_comp_inverse e a a' h
  inv_hom_id := sourceMap_inverse_comp e a a' h

-- The morphisms in `sourceIso` are explicit presentation maps.  Its `sorryAx` is confined to
-- commutative-square, cochain-map, and inverse-law proof fields.

end SheafOfModules.RingedSite.NaiveCotangent.Presentation
