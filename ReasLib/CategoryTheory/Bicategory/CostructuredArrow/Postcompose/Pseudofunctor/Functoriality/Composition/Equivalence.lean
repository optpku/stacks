/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Iso
public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Functoriality.Composition.Component
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic

/-!
# Objectwise equivalence for sequential postcomposition

This leaf upgrades the two explicit components for direct and successive
postcomposition to a bicategorical equivalence of colax costructured arrows.
The object-level equivalence is deliberately separate from strong naturality
in a source costructured-arrow morphism, so it can also be reused by
constructions that only transport individual objects.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y Z : C}

namespace Implementation

/-- The source-map isomorphism of the unit for the sequential-postcomposition
component equivalence. -/
private def postcompose.composition.component.unit.sourceIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        (𝟙 (postcompose.obj (f ≫ g) S)) ≅
      ColaxCostructuredArrow.map (K := K) (X := Z)
        (postcompose.composition.component.hom f g S ≫
          postcompose.composition.component.inv f g S) :=
  (λ_ (𝟙 S.left)).symm

/-- Compatibility of the unit source-map isomorphism with normalized
costructured-arrow comparisons. -/
private theorem postcompose.composition.component.unit.comm
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ((postcompose.obj (f ≫ g) S).comparison S.left).map
          (postcompose.composition.component.unit.sourceIso f g S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Z)
          (postcompose.composition.component.hom f g S ≫
            postcompose.composition.component.inv f g S) =
      ColaxCostructuredArrow.fac (K := K) (X := Z)
        (𝟙 (postcompose.obj (f ≫ g) S)) := sorry

/-- The source-map isomorphism of the counit for the sequential-postcomposition
component equivalence. -/
private def postcompose.composition.component.counit.sourceIso
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map (K := K) (X := Z)
        (postcompose.composition.component.inv f g S ≫
          postcompose.composition.component.hom f g S) ≅
      ColaxCostructuredArrow.map (K := K) (X := Z)
        (𝟙 (postcompose.obj g (postcompose.obj f S))) :=
  λ_ (𝟙 S.left)

/-- Compatibility of the counit source-map isomorphism with normalized
costructured-arrow comparisons. -/
private theorem postcompose.composition.component.counit.comm
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    ((postcompose.obj g (postcompose.obj f S)).comparison S.left).map
          (postcompose.composition.component.counit.sourceIso f g S).hom ≫
        ColaxCostructuredArrow.fac (K := K) (X := Z)
          (𝟙 (postcompose.obj g (postcompose.obj f S))) =
      ColaxCostructuredArrow.fac (K := K) (X := Z)
        (postcompose.composition.component.inv f g S ≫
          postcompose.composition.component.hom f g S) := sorry

end Implementation

/-- The unit isomorphism for the direct-to-successive postcomposition
components at a colax costructured arrow. -/
def postcompose.composition.component.unit
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    𝟙 (postcompose.obj (f ≫ g) S) ≅
      postcompose.composition.component.hom f g S ≫
        postcompose.composition.component.inv f g S :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.postcompose.composition.component.unit.sourceIso f g S)
    (Implementation.postcompose.composition.component.unit.comm f g S)

/-- The counit isomorphism for the direct-to-successive postcomposition
components at a colax costructured arrow. -/
def postcompose.composition.component.counit
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    postcompose.composition.component.inv f g S ≫
        postcompose.composition.component.hom f g S ≅
      𝟙 (postcompose.obj g (postcompose.obj f S)) :=
  ColaxCostructuredArrow.iso₂Mk
    (Implementation.postcompose.composition.component.counit.sourceIso f g S)
    (Implementation.postcompose.composition.component.counit.comm f g S)

/-- The objectwise equivalence from direct postcomposition by `f ≫ g` to
successive postcomposition by `f` and then `g`. -/
def postcompose.composition.component.equivalence
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    postcompose.obj (f ≫ g) S ≌
      postcompose.obj g (postcompose.obj f S) :=
  Bicategory.Equivalence.mkOfAdjointifyUnit
    (postcompose.composition.component.unit f g S)
    (postcompose.composition.component.counit f g S)

/-- The forward morphism of the objectwise sequential-postcomposition
equivalence is the explicit forward component. -/
@[simp]
theorem postcompose.composition.component.equivalence.hom
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.component.equivalence f g S).hom =
      postcompose.composition.component.hom f g S := sorry

/-- The inverse morphism of the objectwise sequential-postcomposition
equivalence is the explicit reverse component. -/
@[simp]
theorem postcompose.composition.component.equivalence.inv
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.component.equivalence f g S).inv =
      postcompose.composition.component.inv f g S := sorry

/-- The unit of the objectwise sequential-postcomposition equivalence is the
canonical adjointification of its explicit unit and counit candidates. -/
@[simp]
theorem postcompose.composition.component.equivalence.unit
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.component.equivalence f g S).unit =
      Bicategory.Equivalence.adjointifyUnit
        (postcompose.composition.component.unit f g S)
        (postcompose.composition.component.counit f g S) := sorry

/-- The counit of the objectwise sequential-postcomposition equivalence is
the explicit counit candidate. -/
@[simp]
theorem postcompose.composition.component.equivalence.counit
    (f : X ⟶ Y) (g : Y ⟶ Z) (S : ColaxCostructuredArrow K X) :
    (postcompose.composition.component.equivalence f g S).counit =
      postcompose.composition.component.counit f g S := sorry

/- Data and axiom audit (mathlib 4.32):

`postcompose.composition.component.equivalence` retains the explicitly constructed forward
and inverse costructured-arrow morphisms. `mkOfAdjointifyUnit` canonically
adjusts the candidate unit against the supplied counit; the public unit and
counit readout theorems expose the resulting data. Deferred obligations are
normalized-comparison compatibility and triangle/coherence laws; no non-Prop
component is hidden. -/

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
