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

/-- The function field of a curve has transcendence degree one over its base field. -/
theorem functionField_trdeg_eq_one_of_curve {k : Type u} [Field k]
    (X : SchemeOverField k) (hX : Curve X) :
    Algebra.trdeg k (SchemeOverField.functionFieldCommAlg X) = 1 := sorry

/-- A curve's function field as an object of the transcendence-degree-one category. -/
noncomputable def curveFunctionFieldObject {k : Type u} [Field k]
    (X : SchemeOverField k) (hX : Curve X) :
    FinitelyGeneratedFieldExtension.TranscendenceDegreeOne.{u, u} k := by
  -- Local instance justification (proof-local temporary data): the function-field
  -- construction reads the curve instance only while assembling this object.
  letI : Curve X := hX
  exact ⟨
    ⟨SchemeOverField.functionFieldCommAlg X,
      ⟨SchemeOverField.functionFieldCommAlg_isField X,
        SchemeOverField.functionField_essFiniteType X⟩⟩,
    functionField_trdeg_eq_one_of_curve X hX⟩

/-- Pullback on function fields induced by a nonconstant morphism of curves. -/
noncomputable def curveFunctionFieldMap {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative]
    {X Y : WideSubcategory (nonconstantHom P)} (f : X ⟶ Y) :
    @SchemeOverField.functionFieldCommAlg k _ Y.obj.obj
        (h_curve Y.obj.obj Y.obj.property).toVariety ⟶
      @SchemeOverField.functionFieldCommAlg k _ X.obj.obj
        (h_curve X.obj.obj X.obj.property).toVariety := by
  -- Local instance justification (proof-local temporary data): the pullback map's
  -- source and target function fields require the curve proofs only in this definition.
  letI : Curve X.obj.obj := h_curve X.obj.obj X.obj.property
  -- Local instance justification (proof-local temporary data): the pullback map's
  -- source and target function fields require the curve proofs only in this definition.
  letI : Curve Y.obj.obj := h_curve Y.obj.obj Y.obj.property
  -- Local instance justification (proof-local temporary data): dominance is derived
  -- from the given nonconstant morphism for the duration of the stalk-map construction.
  letI : IsDominant f.hom.hom.left :=
    Scheme.Hom.IsNonconstant.isDominant_of_curves f.property
  -- Local instance justification (proof-local temporary data): these canonical algebra
  -- structures are needed only to package the explicit pullback as a `CommAlgCat` map.
  letI := SchemeOverField.functionFieldAlgebra X.obj.obj
  -- Local instance justification (proof-local temporary data): these canonical algebra
  -- structures are needed only to package the explicit pullback as a `CommAlgCat` map.
  letI := SchemeOverField.functionFieldAlgebra Y.obj.obj
  exact CommAlgCat.ofHom {
    toRingHom := f.hom.hom.left.functionFieldMap
      (Scheme.Hom.map_genericPoint_eq_of_isDominant f.hom.hom.left)
    commutes' := by sorry
  }

/-- The contravariant function-field functor for any curve category selected by `P`. -/
noncomputable def curveFunctionFieldFunctor {k : Type u} [Field k]
    (P : ObjectProperty (SchemeOverField k))
    (h_curve : ∀ X, P X → Curve X) [h_mul : (nonconstantHom P).IsMultiplicative] :
    WideSubcategory (nonconstantHom P) ⥤
      (FinitelyGeneratedFieldExtension.TranscendenceDegreeOne.{u, u} k)ᵒᵖ where
  obj X := Opposite.op (curveFunctionFieldObject X.obj.obj (h_curve X.obj.obj X.obj.property))
  map f :=
    (ObjectProperty.homMk
      (X := curveFunctionFieldObject _ _) (Y := curveFunctionFieldObject _ _)
      (ObjectProperty.homMk (curveFunctionFieldMap P h_curve f))).op
  map_id := by intros; sorry
  map_comp := by intros; sorry

/-- The function-field functor on curves with dominant rational maps. -/
noncomputable def dominantRationalMapFunctionFieldFunctor {k : Type u} [Field k] :
    DominantRationalMap k ⥤
      (FinitelyGeneratedFieldExtension.TranscendenceDegreeOne.{u, u} k)ᵒᵖ where
  obj X := Opposite.op (curveFunctionFieldObject X.obj.obj X.isCurve)
  map f :=
    (ObjectProperty.homMk
      (X := curveFunctionFieldObject _ _) (Y := curveFunctionFieldObject _ _)
      (ObjectProperty.homMk
        (VarietyDominantRationalMapCat.functionFieldMap f.hom))).op
  map_id := by intros; sorry
  map_comp := by intros; sorry

/-- The function-field functor gives a contravariant equivalence between curves over `k`
with dominant rational maps and finitely generated field extensions of `k` of
transcendence degree one. -/
@[instance]
theorem dominantRationalMapFunctionFieldFunctor_isEquivalence {k : Type u} [Field k] :
    (dominantRationalMapFunctionFieldFunctor (k := k)).IsEquivalence := sorry

/-- The function-field functor gives a contravariant equivalence between normal projective
curves over `k` with nonconstant morphisms and finitely generated field extensions of `k`
of transcendence degree one. -/
@[instance]
theorem normalProjectiveFunctionFieldFunctor_isEquivalence {k : Type u} [Field k] :
    (curveFunctionFieldFunctor (normalProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence := sorry

/-- The function-field functor gives a contravariant equivalence between nonsingular
projective curves over `k` with nonconstant morphisms and finitely generated field
extensions of `k` of transcendence degree one. -/
@[instance]
theorem nonsingularProjectiveFunctionFieldFunctor_isEquivalence {k : Type u} [Field k] :
    (curveFunctionFieldFunctor (nonsingularProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence := sorry

/-- The function-field functor gives a contravariant equivalence between regular projective
curves over `k` with nonconstant morphisms and finitely generated field extensions of `k`
of transcendence degree one. -/
@[instance]
theorem regularProjectiveFunctionFieldFunctor_isEquivalence {k : Type u} [Field k] :
    (curveFunctionFieldFunctor (regularProjectiveProperty k) (fun X hX ↦ hX.1)).IsEquivalence := sorry

/-- The function-field functor gives a contravariant equivalence between normal proper
curves over `k` with nonconstant morphisms and finitely generated field extensions of `k`
of transcendence degree one. -/
@[instance]
theorem normalProperFunctionFieldFunctor_isEquivalence {k : Type u} [Field k] :
    (curveFunctionFieldFunctor (normalProperProperty k) (fun X hX ↦ hX.1)).IsEquivalence := sorry

end AlgebraicGeometry.CurveCategory
