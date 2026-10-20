/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Spaces
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.BaseChange

/-!
# Restriction of formal glueing along morphism properties

Restricting `FormalGlueing.functor` along a morphism property `P` of algebraic
spaces yields a functor from the full subcategory of `Over X` on `P` to the full
subcategory of `Spaces(Y → X, Z)` whose three structure maps satisfy `P`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.FormalGlueing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- The object property on `Spaces(Y → X, Z)` of triples whose structure
morphisms `U' ⟶ U`, `V' ⟶ V`, and `Y' ⟶ Y` all satisfy `P`. -/
abbrev tripleProperty {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] : ObjectProperty (category f i) :=
  fun obj ↦ P obj.fst.hom ∧ P (overlap f i obj).hom ∧ P obj.snd.hom

/-- Membership in `tripleProperty P f i` is `P` on the three structure morphisms
`U' ⟶ U`, `V' ⟶ V`, and `Y' ⟶ Y`. -/
theorem tripleProperty_iff {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (obj : category f i) :
    tripleProperty P f i obj ↔
      P obj.fst.hom ∧ P (overlap f i obj).hom ∧ P obj.snd.hom :=
  sorry

/-- If `P` is stable under base change, then `functor f i` sends a morphism
over `X` satisfying `P` to a triple whose three structure maps satisfy `P`. -/
theorem functor_obj_mem {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [P.IsStableUnderBaseChange] (X' : Over X)
    (hX' : P X'.hom) : tripleProperty P f i ((functor f i).obj X') :=
  sorry

/-- The restriction of `functor f i` to morphisms over `X` satisfying `P`,
landing in the full subcategory of triples whose three structure maps satisfy
`P`. -/
def morphismOverFunctor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [P.IsStableUnderBaseChange] :
    (P.overObj : ObjectProperty (Over X)).FullSubcategory ⥤
      (tripleProperty P f i).FullSubcategory :=
  (tripleProperty P f i).lift
    ((P.overObj : ObjectProperty (Over X)).ι ⋙ functor f i)
    (fun X' ↦ functor_obj_mem P f i X'.obj X'.property)

/-- Composing `morphismOverFunctor P f i` with the inclusion of
`tripleProperty P f i` recovers `ι ⋙ functor f i`. -/
theorem morphismOverFunctor_comp_ι {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [P.IsStableUnderBaseChange] :
    morphismOverFunctor P f i ⋙ (tripleProperty P f i).ι =
      (P.overObj : ObjectProperty (Over X)).ι ⋙ functor f i :=
  sorry

/-- The restriction of `functor f i` to algebraic spaces affine over `X`. -/
abbrev affineOverFunctor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    AffineMorphismOver X ⥤
      (tripleProperty (@AlgebraicSpace.Affine S) f i).FullSubcategory :=
  morphismOverFunctor (@AlgebraicSpace.Affine S) f i

/-- Composing `affineOverFunctor f i` with the inclusion of affine triples
recovers `AffineMorphismOver.inclusion X ⋙ functor f i`. -/
theorem affineOverFunctor_comp_ι {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    affineOverFunctor f i ⋙
        (tripleProperty (@AlgebraicSpace.Affine S) f i).ι =
      AffineMorphismOver.inclusion X ⋙ functor f i :=
  sorry

/-- The restriction of `functor f i` to closed immersions over `X`. -/
abbrev closedImmersionOverFunctor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (MorphismProperty.overObj (@AlgebraicSpace.IsClosedImmersion S) : ObjectProperty (Over X)).FullSubcategory ⥤
      (tripleProperty (@AlgebraicSpace.IsClosedImmersion S) f i).FullSubcategory :=
  morphismOverFunctor (@AlgebraicSpace.IsClosedImmersion S) f i

/-- Composing `closedImmersionOverFunctor f i` with the inclusion of closed
immersion triples recovers `ι ⋙ functor f i` on closed immersions over `X`. -/
theorem closedImmersionOverFunctor_comp_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionOverFunctor f i ⋙
        (tripleProperty (@AlgebraicSpace.IsClosedImmersion S) f i).ι =
      (MorphismProperty.overObj (@AlgebraicSpace.IsClosedImmersion S) : ObjectProperty (Over X)).ι ⋙
        functor f i :=
  sorry

/-- The structure morphism of `X'` is a closed immersion if and only if the
three structure maps of `(functor f i).obj X'` are closed immersions. -/
theorem isClosedImmersion_iff_triple {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    IsClosedImmersion X'.hom ↔
      tripleProperty (@AlgebraicSpace.IsClosedImmersion S) f i ((functor f i).obj X') :=
  sorry

/-- The restriction of `functor f i` to finite morphisms over `X`. -/
abbrev finiteOverFunctor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    (MorphismProperty.overObj (@AlgebraicSpace.IsFinite S) : ObjectProperty (Over X)).FullSubcategory ⥤
      (tripleProperty (@AlgebraicSpace.IsFinite S) f i).FullSubcategory :=
  morphismOverFunctor (@AlgebraicSpace.IsFinite S) f i

/-- Composing `finiteOverFunctor f i` with the inclusion of finite triples
recovers `ι ⋙ functor f i` on finite morphisms over `X`. -/
theorem finiteOverFunctor_comp_ι {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    finiteOverFunctor f i ⋙ (tripleProperty (@AlgebraicSpace.IsFinite S) f i).ι =
      (MorphismProperty.overObj (@AlgebraicSpace.IsFinite S) : ObjectProperty (Over X)).ι ⋙
        functor f i :=
  sorry

/-- The structure morphism of `X'` is finite if and only if the three structure
maps of `(functor f i).obj X'` are finite. -/
theorem isFinite_iff_triple {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    IsFinite X'.hom ↔
      tripleProperty (@AlgebraicSpace.IsFinite S) f i ((functor f i).obj X') :=
  sorry

/-- Under the formal-glueing hypotheses, the canonical functor restricts to an
 equivalence between algebraic spaces affine over `X` and cartesian glueing
 triples whose three structure morphisms are affine. -/
instance affineOverFunctor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (affineOverFunctor f i).IsEquivalence :=
  sorry

/-- Under the formal-glueing hypotheses, the canonical functor restricts to an
 equivalence between closed immersions over `X` and cartesian glueing triples
 whose three structure morphisms are closed immersions. -/
instance closedImmersionOverFunctor_isEquivalence {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (closedImmersionOverFunctor f i).IsEquivalence :=
  sorry

/-- Under the formal-glueing hypotheses, the canonical functor restricts to an
 equivalence between finite morphisms over `X` and cartesian glueing triples
 whose three structure morphisms are finite. -/
instance finiteOverFunctor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (finiteOverFunctor f i).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
