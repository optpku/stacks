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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormalGlueing.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Fpqc
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral

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
  Iff.rfl

/-- If `P` is stable under base change, then `functor f i` sends a morphism
over `X` satisfying `P` to a triple whose three structure maps satisfy `P`. -/
theorem functor_obj_mem {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] [P.IsStableUnderBaseChange] (X' : Over X)
    (hX' : P X'.hom) : tripleProperty P f i ((functor f i).obj X') := by
  have hU := P.baseChange_obj (closedImmersionComplementι i) X' hX'
  exact ⟨hU, P.baseChange_obj (restrictToComplement f i) _ hU,
    P.baseChange_obj f X' hX'⟩

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
  rfl

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
  rfl

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
  rfl

private theorem property_iff_triple_of_isLocalAtTargetFpqc
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget (fpqcPrecoverage S)]
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    P X'.hom ↔ tripleProperty P f i ((functor f i).obj X') := by
  constructor
  · exact functor_obj_mem P f i X'
  · intro h
    have hbase {T W : AlgebraicSpace S} (j : T ⟶ X)
        (hj : P ((Over.pullback j).obj X').hom) (g : W ⟶ X)
        (a : W ⟶ T) (ha : a ≫ j = g) : P ((Over.pullback g).obj X').hom := by
      rw [← ha]
      exact P.overObj.prop_of_iso ((Over.pullbackComp a j).app X').symm
        (P.baseChange_obj a _ hj)
    -- Every member of the refining fpqc cover factors through either `U` or `Y`.
    obtain ⟨𝒰, h𝒰, ⟨r⟩⟩ := IsFormalGlueing.exists_fpqcCovering_refinement f i
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (P := P) (K := fpqcPrecoverage S) (R := 𝒰.toPresieve) ⟨𝒰, h𝒰, rfl⟩
    rintro W g _ ⟨a⟩
    have ha := r.f a
    cases hb : r.α a with
    | false =>
      rw [hb] at ha
      exact hbase (closedImmersionComplementι i) h.1 _ ha.left ha.w
    | true =>
      rw [hb] at ha
      exact hbase f h.2.2 _ ha.left ha.w

/-- The structure morphism of `X'` is a closed immersion if and only if the
three structure maps of `(functor f i).obj X'` are closed immersions. -/
theorem isClosedImmersion_iff_triple {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    IsClosedImmersion X'.hom ↔
      tripleProperty (@AlgebraicSpace.IsClosedImmersion S) f i ((functor f i).obj X') :=
  property_iff_triple_of_isLocalAtTargetFpqc (@AlgebraicSpace.IsClosedImmersion S) f i X'

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
  rfl

/-- The structure morphism of `X'` is finite if and only if the three structure
maps of `(functor f i).obj X'` are finite. -/
theorem isFinite_iff_triple {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (X' : Over X) :
    IsFinite X'.hom ↔
      tripleProperty (@AlgebraicSpace.IsFinite S) f i ((functor f i).obj X') :=
  property_iff_triple_of_isLocalAtTargetFpqc (@AlgebraicSpace.IsFinite S) f i X'

/-- Under the formal-glueing hypotheses, the canonical functor restricts to an
 equivalence between algebraic spaces affine over `X` and cartesian glueing
 triples whose three structure morphisms are affine. -/
instance affineOverFunctor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (affineOverFunctor f i).IsEquivalence :=
  sorry

private theorem morphismOverFunctor_isEquivalence_of_le_affine
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (P : MorphismProperty (AlgebraicSpace S)) (f : Y ⟶ X) (i : Z ⟶ X)
    [P.IsStableUnderBaseChange] [P.RespectsIso]
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] (hP : P ≤ @AlgebraicSpace.Affine S)
    (hiff : ∀ X' : Over X,
      P X'.hom ↔ tripleProperty P f i ((functor f i).obj X')) :
    (morphismOverFunctor P f i).IsEquivalence := by
  have htriple : tripleProperty P f i ≤ tripleProperty (@AlgebraicSpace.Affine S) f i :=
    fun _ h ↦ ⟨hP _ h.1, hP _ h.2.1, hP _ h.2.2⟩
  let inc := ObjectProperty.ιOfLE (show P.overObj ≤ affineMorphismOverProperty X from
    fun _ h ↦ hP _ h)
  let incTriple := ObjectProperty.ιOfLE htriple
  -- The restriction inherits full faithfulness from the affine equivalence.
  haveI : (morphismOverFunctor P f i ⋙ incTriple).Full := by
    change (inc ⋙ affineOverFunctor f i).Full
    infer_instance
  haveI : (morphismOverFunctor P f i ⋙ incTriple).Faithful := by
    change (inc ⋙ affineOverFunctor f i).Faithful
    infer_instance
  refine ⟨Functor.Faithful.of_comp _ incTriple,
    Functor.Full.of_comp_faithful _ incTriple, ⟨?_⟩⟩
  intro T
  -- An affine preimage has `P` by descent and invariance under isomorphisms.
  obtain ⟨X', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (affineOverFunctor f i) (incTriple.obj T)
  let e' : (functor f i).obj X'.obj ≅ T.obj :=
    (tripleProperty (@AlgebraicSpace.Affine S) f i).ι.mapIso e
  let eU := (Limits.CategoricalPullback.π₁ _ _).mapIso e'
  let eY := (Limits.CategoricalPullback.π₂ _ _).mapIso e'
  have hX' : tripleProperty P f i ((functor f i).obj X'.obj) := by
    exact ⟨P.overObj.prop_of_iso eU.symm T.property.1,
      P.overObj.prop_of_iso
        ((Over.pullback (restrictToComplement f i)).mapIso eU).symm T.property.2.1,
      P.overObj.prop_of_iso eY.symm T.property.2.2⟩
  exact ⟨⟨X'.obj, (hiff X'.obj).mpr hX'⟩, ⟨(tripleProperty P f i).isoMk e'⟩⟩

/-- Under the formal-glueing hypotheses, the canonical functor restricts to an
 equivalence between closed immersions over `X` and cartesian glueing triples
 whose three structure morphisms are closed immersions. -/
instance closedImmersionOverFunctor_isEquivalence {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (closedImmersionOverFunctor f i).IsEquivalence :=
  morphismOverFunctor_isEquivalence_of_le_affine
    (@AlgebraicSpace.IsClosedImmersion S) f i IsClosedImmersion.le_affine
    (isClosedImmersion_iff_triple f i)

/-- Under the formal-glueing hypotheses, the canonical functor restricts to an
 equivalence between finite morphisms over `X` and cartesian glueing triples
 whose three structure morphisms are finite. -/
instance finiteOverFunctor_isEquivalence {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] [IsClosedImmersion i] [FinitePresentation i]
    [IsFormalGlueing f i] :
    (finiteOverFunctor f i).IsEquivalence :=
  morphismOverFunctor_isEquivalence_of_le_affine
    (@AlgebraicSpace.IsFinite S) f i
    (by
      intro A B g hg
      letI := hg
      infer_instance)
    (isFinite_iff_triple f i)

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
