/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf

/-!
# Presheaf of relative differential sections

The relative differential sheaf of an object over a scheme gives a presheaf of additive groups
on the opposite of the over-category.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open RingedSpace.Hom.Differentials
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

/-- The additive group of global sections of `Ω[T/S]` for an object `T ⟶ S`. -/
def overObject (S : Scheme.{u}) (U : Over S) : AddCommGrpCat.{u} :=
  RingedSpace.moduleGlobalSections (Ω[U.hom.toShHom])

/-- The square of ringed spaces induced by a morphism in `Over S`. -/
theorem overMap_square {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    f.left.toShHom ≫ V.hom.toShHom =
      U.hom.toShHom ≫ (𝟙 S : S ⟶ S).toShHom := sorry

/-- Pullback of relative-differential global sections along a map in `Over S`. -/
noncomputable def overMap {S : Scheme.{u}} {U V : Over S} (f : U ⟶ V) :
    overObject S V ⟶ overObject S U :=
  RingedSpace.Hom.globalSectionsPullback f.left.toShHom Ω[V.hom.toShHom] ≫
    RingedSpace.moduleGlobalSectionsMap
      (comparison (CommSq.mk (overMap_square f)))

/-- Pullback of relative-differential sections preserves identities. -/
theorem overMap_id {S : Scheme.{u}} (U : Over S) :
    overMap (𝟙 U) = 𝟙 (overObject S U) := sorry

/-- Pullback of relative-differential sections reverses composition. -/
theorem overMap_comp {S : Scheme.{u}} {U V W : Over S}
    (f : U ⟶ V) (g : V ⟶ W) :
    overMap (f ≫ g) = overMap g ≫ overMap f := sorry

/-- The opposite-category composition law used by the presheaf constructor. -/
theorem overMap_comp_op {S : Scheme.{u}} {U V W : (Over S)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    overMap (f ≫ g).unop = overMap f.unop ≫ overMap g.unop := sorry

/-- The presheaf of global sections of relative differentials on `(Over S)ᵒᵖ`. -/
noncomputable def differentialFormsPresheaf (S : Scheme.{u}) :
    (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := overObject S U.unop
  map f := overMap f.unop
  map_id U := overMap_id U.unop
  map_comp f g := overMap_comp_op f g

/-- The presheaf of relative differential sections is a sheaf for the Zariski topology. -/
theorem differentialFormsPresheaf_isSheaf_zariski (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S)
      (differentialFormsPresheaf S ⋙ CategoryTheory.forget AddCommGrpCat) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
