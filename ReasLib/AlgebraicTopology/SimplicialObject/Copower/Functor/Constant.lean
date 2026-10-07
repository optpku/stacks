module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Object
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Copowers of constant simplicial objects

For a fixed simplicial set, copower restricts to a functor from the ambient category through the
constant simplicial-object functor.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (U : SSet.{w})
variable [HasConstCopowers U C]

/-- The copower morphism induced by a morphism between constant simplicial objects. -/
@[stacks 017J "constant-object copower morphism"]
def copower.constFunctor.mapHom {X Y : C} (f : X ⟶ Y) :
    copower U ((const C).obj X) ⟶ copower U ((const C).obj Y) :=
  copower.hom U ((const C).map f)

/-- Constant-object copower morphisms preserve identities. -/
@[stacks 017J "constant-object copower identity law"]
theorem copower.constFunctor.mapHom.id (X : C) :
    copower.constFunctor.mapHom U (𝟙 X) =
      𝟙 (copower U ((const C).obj X)) := sorry

/-- Constant-object copower morphisms preserve composition. -/
@[stacks 017J "constant-object copower composition law"]
theorem copower.constFunctor.mapHom.comp {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    copower.constFunctor.mapHom U (f ≫ g) =
      copower.constFunctor.mapHom U f ≫ copower.constFunctor.mapHom U g := sorry

/-- Copower by `U`, restricted to constant simplicial objects. This is the exact functor needed
to test a simplicial mapping object on objects of `C`; it does not require copowers of arbitrary
simplicial objects. -/
@[stacks 017J "copower of constant simplicial objects"]
def copower.constFunctor : C ⥤ SimplicialObject C where
  obj X := copower U ((const C).obj X)
  map f := copower.constFunctor.mapHom U f
  map_id X := copower.constFunctor.mapHom.id U X
  map_comp f g := copower.constFunctor.mapHom.comp U f g

/-- The object part of `copower.constFunctor U` is the copower of the corresponding constant
simplicial object. -/
@[simp, stacks 017J "constant-object copower formula"]
theorem copower.constFunctor.obj (X : C) :
    (copower.constFunctor U).obj X = copower U ((const C).obj X) := sorry

/-- The map part of `copower.constFunctor U` is induced by the constant simplicial morphism. -/
@[simp, stacks 017J "constant-object copower map formula"]
theorem copower.constFunctor.map {X Y : C} (f : X ⟶ Y) :
    (copower.constFunctor U).map f = copower.hom U ((const C).map f) := sorry

end CategoryTheory.SimplicialObject
