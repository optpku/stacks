/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily

/-!
# Fibre comparison maps for families of cycles

This file records the scheme-theoretic fibre identifications used to move
cycles between a base change, an open restriction, and a fibre of a morphism
over `S`, together with the fibrewise morphism instances those operations need.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The constant-zero function is a dimension function on the spectrum of a
residue field. -/
instance instIsDimensionFunction_zero_specResidueField {X : Scheme.{u}} (x : X) :
    IsDimensionFunction (fun _ : Spec (X.residueField x) ↦ (0 : ℤ)) := sorry

/-- The spectrum map of a residue-field homomorphism is flat. -/
instance instFlat_residueFieldSpecMap {S S' : Scheme.{u}} (g : S' ⟶ S) (s' : S') :
    Flat (Spec.map (g.residueFieldMap s')) :=
  (Flat.SpecMap_iff (f := g.residueFieldMap s')).2
    (RingHom.Flat.of_isField (Field.toIsField _) (g.residueFieldMap s').hom)

/-- Residue-field spectrum maps are compatible with the constant-zero dimension
functions, with shift `0`. -/
theorem isDimensionFunctionCompatible_residueFieldSpecMap
    {S S' : Scheme.{u}} (g : S' ⟶ S) (s' : S') :
    IsDimensionFunctionCompatible (Spec.map (g.residueFieldMap s'))
      (fun _ ↦ 0) (fun _ ↦ 0) 0 := sorry

/-- The fibre map of a commutative square is locally of finite type when the
source map is locally of finite type and the base map is an isomorphism. -/
instance instLocallyOfFiniteType_fiberMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) [IsIso g] [LocallyOfFiniteType i] (s' : S') :
    LocallyOfFiniteType (fiberMap f' i g f sq s') := sorry

/-- The fibre map of a commutative square is flat when the source map is flat
and the base map is an isomorphism. -/
instance instFlat_fiberMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) [IsIso g] [Flat i] (s' : S') :
    Flat (fiberMap f' i g f sq s') := sorry

/-- The fibre map of a commutative square is proper when the source map is
proper and the base map is an isomorphism. -/
instance instIsProper_fiberMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) [IsIso g] [IsProper i] (s' : S') :
    IsProper (fiberMap f' i g f sq s') := sorry

/-- The fibre map of a commutative square has the same relative dimension as
the source map when the base map is an isomorphism. -/
instance instRelativeDimension_fiberMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) [IsIso g] (e : ℕ) [RelativeDimension i e] (s' : S') :
    RelativeDimension (fiberMap f' i g f sq s') e := sorry

/-- The fibre map of a square of open immersions is an open immersion. -/
instance instIsOpenImmersion_fiberMap {X' S' X S : Scheme.{u}}
    (f' : X' ⟶ S') (i : X' ⟶ X) (g : S' ⟶ S) (f : X ⟶ S)
    (sq : CommSq i f' f g) [IsOpenImmersion i] [IsOpenImmersion g] (s' : S') :
    IsOpenImmersion (fiberMap f' i g f sq s') := sorry

/-- The identification `X'_{s'} ≅ X_{g(s')} ×_{Spec κ(g(s'))} Spec κ(s')` of
scheme-theoretic fibres induced by a cartesian square. -/
noncomputable def fiberBaseChangeIso {S X S' X' : Scheme.{u}}
    (f : X ⟶ S) (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (hpb : IsPullback g' f' f g) (s' : S') :
    pullback (f.fiberToSpecResidueField (g s')) (Spec.map (g.residueFieldMap s')) ≅
      f'.fiber s' :=
  (isPullback_fiberToSpecResidueField_of_isPullback hpb s').isoPullback.symm

/-- The open of the scheme-theoretic fibre `X_s` cut out by an open `U ⊆ X`. -/
def fiberOpen {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (s : S) :
    (f.fiber s).Opens :=
  f.fiberι s ⁻¹ᵁ U

/-- The commutative square of a restriction `f.resLE V U`. -/
theorem commSq_resLE {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (hU : U ≤ f ⁻¹ᵁ V) : CommSq U.ι (f.resLE V U hU) f V.ι :=
  ⟨(resLE_comp_ι f hU).symm⟩

/-- The comparison morphism from the fibre of a restriction to the original
fibre. -/
noncomputable abbrev resLEFiberMap {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    (f.resLE V U hU).fiber s ⟶ f.fiber (V.ι s) :=
  fiberMap (f.resLE V U hU) U.ι V.ι f (commSq_resLE f U V hU) s

/-- The image of `resLEFiberMap` is contained in the open of the fibre cut out
by `U`. -/
theorem resLEFiberMap_range_subset_fiberOpen {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    Set.range (resLEFiberMap f U V hU s) ⊆ Set.range (fiberOpen f U (V.ι s)).ι := by
  have hι : resLEFiberMap f U V hU s ≫ f.fiberι (V.ι s) =
      (f.resLE V U hU).fiberι s ≫ U.ι := by
    dsimp only [resLEFiberMap, fiberMap, Scheme.Hom.fiberι, pullback.map]
    exact pullback.lift_fst _ _ _
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨resLEFiberMap f U V hU s x, ?_⟩, rfl⟩
  change f.fiberι (V.ι s) (resLEFiberMap f U V hU s x) ∈ U
  rw [← Scheme.Hom.comp_apply, hι, Scheme.Hom.comp_apply]
  exact ((f.resLE V U hU).fiberι s x).property

/-- The open of the fibre cut out by `U` is contained in the image of
`resLEFiberMap`. -/
theorem fiberOpen_range_subset_resLEFiberMap {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    Set.range (fiberOpen f U (V.ι s)).ι ⊆ Set.range (resLEFiberMap f U V hU s) :=
  sorry

/-- The forward lift from a restriction fibre to the open cut out by `U` in
the original fibre. -/
noncomputable def resLEFiberHom {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    (f.resLE V U hU).fiber s ⟶ (fiberOpen f U (V.ι s)).toScheme :=
  IsOpenImmersion.lift (fiberOpen f U (V.ι s)).ι (resLEFiberMap f U V hU s)
    (resLEFiberMap_range_subset_fiberOpen f U V hU s)

/-- The inverse lift from the open cut out by `U` in the original fibre to
the restriction fibre. -/
noncomputable def resLEFiberInv {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    (fiberOpen f U (V.ι s)).toScheme ⟶ (f.resLE V U hU).fiber s := by
  let W := fiberOpen f U (V.ι s)
  let m := Spec.map (V.ι.residueFieldMap s)
  letI : IsIso m := by
    dsimp only [m]
    infer_instance
  let p₁ := (f.fiberι (V.ι s)).resLE U W le_rfl
  let p₂ := W.ι ≫ f.fiberToSpecResidueField (V.ι s) ≫ inv m
  refine pullback.lift p₁ p₂ ?_
  apply (cancel_mono V.ι).1
  calc
    (p₁ ≫ f.resLE V U hU) ≫ V.ι = W.ι ≫ f.fiberι (V.ι s) ≫ f := by
      dsimp only [p₁]
      rw [Category.assoc, Scheme.Hom.resLE_comp_ι,
        ← Category.assoc, Scheme.Hom.resLE_comp_ι]
      exact Category.assoc _ _ _
    _ = W.ι ≫ f.fiberToSpecResidueField (V.ι s) ≫ S.fromSpecResidueField (V.ι s) := by
      rw [f.fiber_fac (V.ι s)]
    _ = (p₂ ≫ V.toScheme.fromSpecResidueField s) ≫ V.ι := by
      dsimp only [p₂]
      rw [Category.assoc, Category.assoc, Category.assoc,
        ← V.ι.SpecMap_residueFieldMap_fromSpecResidueField s]
      simp [m]

/-- The forward restriction-fibre lift followed by its inverse is the identity. -/
theorem resLEFiberHom_inv_id {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    resLEFiberHom f U V hU s ≫ resLEFiberInv f U V hU s =
      𝟙 ((f.resLE V U hU).fiber s) := sorry

/-- The inverse restriction-fibre lift followed by the forward lift is the identity. -/
theorem resLEFiberInv_hom_id {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    resLEFiberInv f U V hU s ≫ resLEFiberHom f U V hU s =
      𝟙 (fiberOpen f U (V.ι s)).toScheme := sorry

/-- The identification of the fibre of `f.resLE V U` at `s` with the open of
the fibre `X_{V.ι s}` cut out by `U`. -/
noncomputable def resLEFiberIso {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)
    (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) (s : V.toScheme) :
    (f.resLE V U hU).fiber s ≅ (fiberOpen f U (V.ι s)).toScheme where
  hom := resLEFiberHom f U V hU s
  inv := resLEFiberInv f U V hU s
  hom_inv_id := resLEFiberHom_inv_id f U V hU s
  inv_hom_id := resLEFiberInv_hom_id f U V hU s

/-- The commutative square of a triangle over `S`. -/
theorem commSq_idTriangle {X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    (h : X' ⟶ X) (hf : h ≫ f = f') : CommSq h f' f (𝟙 S) := sorry

/-- The morphism of scheme-theoretic fibres induced by a triangle over `S`. -/
noncomputable def idTriangleFiberMap {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f') (s : S) :
    f'.fiber s ⟶ f.fiber s :=
  fiberMap f' h (𝟙 S) f (commSq_idTriangle h hf) s

/-- Unfolding the fibre map of a triangle over `S`. -/
theorem idTriangleFiberMap_eq {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f') (s : S) :
    idTriangleFiberMap h hf s =
      fiberMap f' h (𝟙 S) f (commSq_idTriangle h hf) s := sorry

/-- The fibre map of a triangle over `S` is flat when the original morphism is. -/
instance instFlat_idTriangleFiberMap {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f')
    [Flat h] (s : S) : Flat (idTriangleFiberMap h hf s) := sorry

/-- The fibre map of a triangle over `S` has the same relative dimension as the
original morphism. -/
instance instRelativeDimension_idTriangleFiberMap {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f') (e : ℕ)
    [RelativeDimension h e] (s : S) :
    RelativeDimension (idTriangleFiberMap h hf s) e := sorry

/-- The fibre map of a triangle over `S` is proper when the original morphism
is. -/
instance instIsProper_idTriangleFiberMap {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f')
    [IsProper h] (s : S) : IsProper (idTriangleFiberMap h hf s) := sorry

/-- The fibre map of a triangle over `S` is quasicompact when the original
morphism is. -/
instance instQuasiCompact_idTriangleFiberMap {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f')
    [QuasiCompact h] (s : S) : QuasiCompact (idTriangleFiberMap h hf s) := sorry

/-- The fibre map of a triangle over `S` commutes with the residue-field
structure morphisms. -/
theorem idTriangleFiberMap_fiberToSpecResidueField {X' X S : Scheme.{u}}
    {f : X ⟶ S} {f' : X' ⟶ S} (h : X' ⟶ X) (hf : h ≫ f = f') (s : S) :
    idTriangleFiberMap h hf s ≫ f.fiberToSpecResidueField s =
      f'.fiberToSpecResidueField s := sorry

/-- The restriction `f.resLE V U` is the nested open of `f ∣_ V`. -/
theorem resLE_eq_homOfLE_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) :
    X.homOfLE hU ≫ f ∣_ V = f.resLE V U hU := sorry

/-- Pasting two triangles over `S` yields a triangle for the composite. -/
theorem triangle_comp {X'' X' X S : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S}
    {f'' : X'' ⟶ S} {k : X' ⟶ X} {h : X'' ⟶ X'}
    (hk : k ≫ f = f') (hh : h ≫ f' = f'') : (h ≫ k) ≫ f = f'' := sorry

end AlgebraicGeometry.Scheme.Hom
