/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.FunctionField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FinitelyGeneratedFieldExtension

/-- The object property of having transcendence degree one over the base field. -/
def trdegOneProperty (k : Type u) [Field k] : ObjectProperty (Cat k) :=
  fun K ↦ Algebra.trdeg k K.obj = 1

/-- Finitely generated field extensions of `k` of transcendence degree one. -/
abbrev TranscendenceDegreeOne (k : Type u) [Field k] :=
  (trdegOneProperty k).FullSubcategory

/-- An object of `TranscendenceDegreeOne k` has transcendence degree one over `k`. -/
theorem TranscendenceDegreeOne.trdeg_eq_one {k : Type u} [Field k]
    (K : TranscendenceDegreeOne k) : Algebra.trdeg k K.obj.obj = 1 := sorry

end AlgebraicGeometry.FinitelyGeneratedFieldExtension

namespace AlgebraicGeometry.CurveCategory

/-- The object property selecting curves inside the category of varieties with dominant rational maps. -/
def dominantRationalMapProperty (k : Type u) [Field k] :
    ObjectProperty (VarietyDominantRationalMapCat k) :=
  fun X ↦ Curve X.obj

/-- Curves over `k` and dominant rational maps. -/
abbrev DominantRationalMap (k : Type u) [Field k] :=
  (dominantRationalMapProperty k).FullSubcategory

/-- The scheme underlying an object of `DominantRationalMap k` is a curve. -/
theorem DominantRationalMap.isCurve {k : Type u} [Field k]
    (X : DominantRationalMap k) : Curve X.obj.obj := sorry

/-- The morphism property selecting nonconstant maps between schemes over a field satisfying an object property `P`. -/
def nonconstantHom {k : Type u} [Field k] (P : ObjectProperty (SchemeOverField k)) :
    MorphismProperty P.FullSubcategory :=
  fun _ _ f ↦ f.hom.left.IsNonconstant

/-- Membership in `nonconstantHom P` is exactly nonconstancy of the underlying scheme morphism. -/
theorem nonconstantHom_iff {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k)) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    nonconstantHom P f ↔ f.hom.left.IsNonconstant := sorry

/-- The curve over `k` underlying an object of a nonconstant-morphism category selected by an object property `P`. -/
def toDominantRationalMapObj {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    (X : WideSubcategory (nonconstantHom P)) : DominantRationalMap k :=
  ⟨⟨X.obj.obj, (h_curve X.obj.obj X.obj.property).toVariety⟩,
    h_curve X.obj.obj X.obj.property⟩

/-- The rational map underlying a nonconstant morphism between curves is over the base field. -/
theorem toDominantRationalMapMap_isOver {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    {X Y : WideSubcategory (nonconstantHom P)} (f : X ⟶ Y) :
    f.hom.hom.left.toRationalMap.IsOver (Spec (CommRingCat.of k)) := sorry

/-- The rational map underlying a nonconstant morphism between curves is dominant. -/
theorem toDominantRationalMapMap_isDominant {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    {X Y : WideSubcategory (nonconstantHom P)} (f : X ⟶ Y) :
    f.hom.hom.left.toRationalMap.IsDominant := sorry

/-- Send a nonconstant morphism between curves to its dominant rational map. -/
noncomputable def toDominantRationalMapMap {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    {X Y : WideSubcategory (nonconstantHom P)} (f : X ⟶ Y) :
    toDominantRationalMapObj P h_curve X ⟶ toDominantRationalMapObj P h_curve Y :=
  ObjectProperty.homMk
    ⟨f.hom.hom.left.toRationalMap,
      toDominantRationalMapMap_isOver P h_curve f,
      toDominantRationalMapMap_isDominant P h_curve f⟩

/-- The rational-map construction preserves identity morphisms. -/
theorem toDominantRationalMapMap_id {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    (X : WideSubcategory (nonconstantHom P)) :
    toDominantRationalMapMap P h_curve (𝟙 X) =
      𝟙 (toDominantRationalMapObj P h_curve X) := sorry

/-- The rational-map construction preserves composition. -/
theorem toDominantRationalMapMap_comp {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    {X Y Z : WideSubcategory (nonconstantHom P)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toDominantRationalMapMap P h_curve (f ≫ g) =
      toDominantRationalMapMap P h_curve f ≫ toDominantRationalMapMap P h_curve g := sorry

/-- The functor from curves and nonconstant morphisms to curves and dominant rational maps. -/
noncomputable def toDominantRationalMap {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative] :
    WideSubcategory (nonconstantHom P) ⥤ DominantRationalMap k where
  obj := toDominantRationalMapObj P h_curve
  map := toDominantRationalMapMap P h_curve
  map_id := toDominantRationalMapMap_id P h_curve
  map_comp := toDominantRationalMapMap_comp P h_curve

/-- The object action of `toDominantRationalMap` retains the underlying curve. -/
theorem toDominantRationalMap_obj_obj {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    (X : WideSubcategory (nonconstantHom P)) :
    ((toDominantRationalMap P h_curve).obj X).obj.obj = X.obj.obj := sorry

/-- The morphism action of `toDominantRationalMap` is the underlying rational map. -/
theorem toDominantRationalMap_map_hom {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    {X Y : WideSubcategory (nonconstantHom P)} (f : X ⟶ Y) :
    ((toDominantRationalMap P h_curve).map f).hom.1 =
      f.hom.hom.left.toRationalMap := sorry

/-- The property of being a normal projective curve over `k`. -/
def normalProjectiveProperty (k : Type u) [Field k] : ObjectProperty (SchemeOverField k) :=
  fun X ↦ Curve X ∧ X.left.isNormal ∧ Projective X.hom

/-- Nonconstant morphisms of normal projective curves are closed under identities and composition. -/
instance instNormalProjectiveNonconstantHomIsMultiplicative (k : Type u) [Field k] :
    (nonconstantHom (normalProjectiveProperty k)).IsMultiplicative := sorry

/-- Normal projective curves over `k` and nonconstant morphisms. -/
abbrev NormalProjective (k : Type u) [Field k] :=
  WideSubcategory (nonconstantHom (normalProjectiveProperty k))

/-- The object conditions in the category of normal projective curves. -/
theorem NormalProjective.obj_spec {k : Type u} [Field k] (X : NormalProjective k) :
    Curve X.obj.obj ∧ X.obj.obj.left.isNormal ∧ Projective X.obj.obj.hom := sorry

/-- The property of being a nonsingular projective curve over `k`, with nonsingularity expressed by regularity. -/
def nonsingularProjectiveProperty (k : Type u) [Field k] :
    ObjectProperty (SchemeOverField k) :=
  fun X ↦ Curve X ∧ Scheme.Regular X.left ∧ Projective X.hom

/-- Nonconstant morphisms of nonsingular projective curves are closed under identities and composition. -/
instance instNonsingularProjectiveNonconstantHomIsMultiplicative (k : Type u) [Field k] :
    (nonconstantHom (nonsingularProjectiveProperty k)).IsMultiplicative := sorry

/-- Nonsingular projective curves over `k` and nonconstant morphisms. -/
abbrev NonsingularProjective (k : Type u) [Field k] :=
  WideSubcategory (nonconstantHom (nonsingularProjectiveProperty k))

/-- The object conditions in the category of nonsingular projective curves. -/
theorem NonsingularProjective.obj_spec {k : Type u} [Field k]
    (X : NonsingularProjective k) :
    Curve X.obj.obj ∧ Scheme.Regular X.obj.obj.left ∧ Projective X.obj.obj.hom := sorry

/-- The property of being a regular projective curve over `k`. -/
def regularProjectiveProperty (k : Type u) [Field k] : ObjectProperty (SchemeOverField k) :=
  fun X ↦ Curve X ∧ Scheme.Regular X.left ∧ Projective X.hom

/-- Nonconstant morphisms of regular projective curves are closed under identities and composition. -/
instance instRegularProjectiveNonconstantHomIsMultiplicative (k : Type u) [Field k] :
    (nonconstantHom (regularProjectiveProperty k)).IsMultiplicative := sorry

/-- Regular projective curves over `k` and nonconstant morphisms. -/
abbrev RegularProjective (k : Type u) [Field k] :=
  WideSubcategory (nonconstantHom (regularProjectiveProperty k))

/-- The object conditions in the category of regular projective curves. -/
theorem RegularProjective.obj_spec {k : Type u} [Field k] (X : RegularProjective k) :
    Curve X.obj.obj ∧ Scheme.Regular X.obj.obj.left ∧ Projective X.obj.obj.hom := sorry

/-- The property of being a normal proper curve over `k`. -/
def normalProperProperty (k : Type u) [Field k] : ObjectProperty (SchemeOverField k) :=
  fun X ↦ Curve X ∧ X.left.isNormal ∧ IsProper X.hom

/-- Nonconstant morphisms of normal proper curves are closed under identities and composition. -/
instance instNormalProperNonconstantHomIsMultiplicative (k : Type u) [Field k] :
    (nonconstantHom (normalProperProperty k)).IsMultiplicative := sorry

/-- Normal proper curves over `k` and nonconstant morphisms. -/
abbrev NormalProper (k : Type u) [Field k] :=
  WideSubcategory (nonconstantHom (normalProperProperty k))

/-- The object conditions in the category of normal proper curves. -/
theorem NormalProper.obj_spec {k : Type u} [Field k] (X : NormalProper k) :
    Curve X.obj.obj ∧ X.obj.obj.left.isNormal ∧ IsProper X.obj.obj.hom := sorry

/-- One-variable function fields over `k` are equivalent to curves with dominant rational maps. -/
theorem oneVariableFunctionFieldsEquivCurveRationalMaps (k : Type u) [Field k] :
    Nonempty
      ((FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
        DominantRationalMap k) := sorry

/-- One-variable function fields over `k` are equivalent to normal projective curves. -/
theorem oneVariableFunctionFieldsEquivNormalProjectiveCurves (k : Type u) [Field k] :
    Nonempty
      ((FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
        NormalProjective k) := sorry

/-- One-variable function fields over `k` are equivalent to nonsingular projective curves. -/
theorem oneVariableFunctionFieldsEquivNonsingularProjectiveCurves (k : Type u) [Field k] :
    Nonempty
      ((FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
        NonsingularProjective k) := sorry

/-- One-variable function fields over `k` are equivalent to regular projective curves. -/
theorem oneVariableFunctionFieldsEquivRegularProjectiveCurves (k : Type u) [Field k] :
    Nonempty
      ((FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
        RegularProjective k) := sorry

/-- One-variable function fields over `k` are equivalent to normal proper curves. -/
theorem oneVariableFunctionFieldsEquivNormalProperCurves (k : Type u) [Field k] :
    Nonempty
      ((FinitelyGeneratedFieldExtension.TranscendenceDegreeOne k)ᵒᵖ ≌
        NormalProper k) := sorry

end AlgebraicGeometry.CurveCategory
