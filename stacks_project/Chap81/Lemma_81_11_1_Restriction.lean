module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import stacks_project.Chap67.Lemma_67_20_5
public import stacks_project.Chap67.Lemma_67_20_7_AffineOver
public import stacks_project.Chap67.Lemma_67_45_5
public import stacks_project.Chap81.«81_11_0_1_Glueing»
public import stacks_project.Chap81.Situation_81_10_6_FormalGlueing

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

/-- The morphism property of closed immersions of algebraic spaces over `S`. -/
abbrev closedImmersionProperty (S : Scheme.{u}) : MorphismProperty (AlgebraicSpace S) :=
  @AlgebraicSpace.IsClosedImmersion S

/-- Membership in `closedImmersionProperty S` is the class `IsClosedImmersion`. -/
theorem closedImmersionProperty_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : closedImmersionProperty S f ↔ IsClosedImmersion f :=
  sorry

/-- Closed immersions of algebraic spaces are stable under base change.
This records Lemma 65.12.3 (2) in the formal-glueing import graph, which cannot
import that lemma because `IsClosedImmersion.of_isPullback` collides. -/
instance instIsClosedImmersion_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange (closedImmersionProperty S) :=
  sorry

/-- The morphism property of finite morphisms of algebraic spaces over `S`. -/
abbrev finiteMorphismProperty (S : Scheme.{u}) : MorphismProperty (AlgebraicSpace S) :=
  @AlgebraicSpace.IsFinite S

/-- Membership in `finiteMorphismProperty S` is the class `IsFinite`. -/
theorem finiteMorphismProperty_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : finiteMorphismProperty S f ↔ IsFinite f :=
  sorry

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
    ((closedImmersionProperty S).overObj : ObjectProperty (Over X)).FullSubcategory ⥤
      (tripleProperty (closedImmersionProperty S) f i).FullSubcategory :=
  morphismOverFunctor (closedImmersionProperty S) f i

/-- Composing `closedImmersionOverFunctor f i` with the inclusion of closed
immersion triples recovers `ι ⋙ functor f i` on closed immersions over `X`. -/
theorem closedImmersionOverFunctor_comp_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    closedImmersionOverFunctor f i ⋙
        (tripleProperty (closedImmersionProperty S) f i).ι =
      ((closedImmersionProperty S).overObj : ObjectProperty (Over X)).ι ⋙
        functor f i :=
  sorry

/-- The structure morphism of `X'` is a closed immersion if and only if the
three structure maps of `(functor f i).obj X'` are closed immersions. -/
theorem isClosedImmersion_iff_triple {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    IsClosedImmersion X'.hom ↔
      tripleProperty (closedImmersionProperty S) f i ((functor f i).obj X') :=
  sorry

/-- The restriction of `functor f i` to finite morphisms over `X`. -/
abbrev finiteOverFunctor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    ((finiteMorphismProperty S).overObj : ObjectProperty (Over X)).FullSubcategory ⥤
      (tripleProperty (finiteMorphismProperty S) f i).FullSubcategory :=
  morphismOverFunctor (finiteMorphismProperty S) f i

/-- Composing `finiteOverFunctor f i` with the inclusion of finite triples
recovers `ι ⋙ functor f i` on finite morphisms over `X`. -/
theorem finiteOverFunctor_comp_ι {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i] :
    finiteOverFunctor f i ⋙ (tripleProperty (finiteMorphismProperty S) f i).ι =
      ((finiteMorphismProperty S).overObj : ObjectProperty (Over X)).ι ⋙
        functor f i :=
  sorry

/-- The structure morphism of `X'` is finite if and only if the three structure
maps of `(functor f i).obj X'` are finite. -/
theorem isFinite_iff_triple {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    IsFinite X'.hom ↔
      tripleProperty (finiteMorphismProperty S) f i ((functor f i).obj X') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
