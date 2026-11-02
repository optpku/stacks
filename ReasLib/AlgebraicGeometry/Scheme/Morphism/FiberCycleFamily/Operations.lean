/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Along
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Composition
public import ReasLib.AlgebraicGeometry.CycleGroup.Localization
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Comparison

/-!
# Operations on families of cycles on fibres

This file defines base change, restriction, flat pullback, and proper
pushforward of a family of cycles on scheme-theoretic fibres, by applying the
corresponding CycleGroup maps fibrewise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.FiberCycleFamily

/-- Transport a family of fibre cycles along an equality of its degree. -/
noncomputable def reindex {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {a b : ℤ} (h : a = b)
    (α : f.FiberCycleFamily a) : f.FiberCycleFamily b :=
  fun s ↦ CycleGroup.reindex (f.fiberRelativeDimensionFunction s) h (α s)

/-- Evaluating a reindexed family transports the cycle on that fibre. -/
theorem reindex_apply {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {a b : ℤ} (h : a = b) (α : f.FiberCycleFamily a) (s : S) :
    reindex h α s = CycleGroup.reindex (f.fiberRelativeDimensionFunction s) h (α s) := rfl

/-- Degree transport preserves the zero family of fibre cycles. -/
theorem reindex_zero {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {a b : ℤ} (h : a = b) : reindex h (0 : f.FiberCycleFamily a) = 0 := by
  funext s
  exact (CycleGroup.reindex (f.fiberRelativeDimensionFunction s) h).map_zero

/-- Degree transport preserves addition of families of fibre cycles. -/
theorem reindex_add {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    {a b : ℤ} (h : a = b) (α β : f.FiberCycleFamily a) :
    reindex h (α + β) = reindex h α + reindex h β := by
  funext s
  exact (CycleGroup.reindex (f.fiberRelativeDimensionFunction s) h).map_add (α s) (β s)

/-- The underlying map of `Over.homMk φ` is flat when `φ` is flat. -/
instance instFlat_overHomMk {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
    (φ : X ⟶ Y) (hφ : φ ≫ pY = pX) [Flat φ] :
    Flat (Over.homMk φ hφ : Over.mk pX ⟶ Over.mk pY).left :=
  inferInstanceAs (Flat φ)

/-- The underlying map of `Over.homMk φ` has the same relative dimension as `φ`. -/
instance instRelativeDimension_overHomMk {S X Y : Scheme.{u}} {pX : X ⟶ S}
    {pY : Y ⟶ S} (φ : X ⟶ Y) (hφ : φ ≫ pY = pX) (e : ℕ)
    [RelativeDimension φ e] :
    RelativeDimension (Over.homMk φ hφ : Over.mk pX ⟶ Over.mk pY).left e :=
  inferInstanceAs (RelativeDimension φ e)

/-- Flat pullback of a cycle along a morphism of fibres over `Spec κ(s)`. -/
noncomputable def fiberwiseFlatPullback {S : Scheme.{u}} (s : S)
    {Xs Xt : Scheme.{u}}
    (pX : Xs ⟶ Spec (S.residueField s)) [LocallyOfFiniteType pX]
    (pY : Xt ⟶ Spec (S.residueField s)) [LocallyOfFiniteType pY]

    (φ : Xs ⟶ Xt) (hφ : φ ≫ pY = pX) (e : ℕ)
    [Flat φ] [RelativeDimension φ e] {r : ℤ}
    (α : CycleGroup Xt (pY.relativeDimensionFunction (fun _ ↦ 0)) r) :
    CycleGroup Xs (pX.relativeDimensionFunction (fun _ ↦ 0)) (r + (e : ℤ)) :=
  CycleGroup.flatPullbackAlong (fun _ ↦ 0) pX pY φ hφ e r α

/-- Proper pushforward of a cycle along a morphism of fibres over `Spec κ(s)`. -/
noncomputable def fiberwisePushforward {S : Scheme.{u}} (s : S)
    {Xs Xt : Scheme.{u}}
    (pX : Xs ⟶ Spec (S.residueField s)) [LocallyOfFiniteType pX]
    (pY : Xt ⟶ Spec (S.residueField s)) [LocallyOfFiniteType pY]
    (φ : Xs ⟶ Xt) [QuasiCompact φ] {r : ℤ}
    (α : CycleGroup Xs (pX.relativeDimensionFunction (fun _ ↦ 0)) r) :
    CycleGroup Xt (pY.relativeDimensionFunction (fun _ ↦ 0)) r :=
  CycleGroup.mapHom φ (pX.relativeDimensionFunction (fun _ ↦ 0))
    (pY.relativeDimensionFunction (fun _ ↦ 0)) r α

/-- Base change of a family of fibre cycles along a cartesian square. -/
noncomputable def baseChange {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : f.FiberCycleFamily r) :
    @Scheme.Hom.FiberCycleFamily _ _ f'
      (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance) r :=
  fun s' ↦
    CycleGroup.mapHom
      (fiberBaseChangeIso f g g' f' hpb s').hom
      ((pullback.snd (f.fiberToSpecResidueField (g s'))
          (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
        (fun _ ↦ 0))
      (@Scheme.Hom.fiberRelativeDimensionFunction _ _ f'
          (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance) s') r
      (CycleGroup.reindex
        ((pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0))
        (add_zero r)
        (CycleGroup.baseChangePullback
          (Spec.map (g.residueFieldMap s')) (fun _ ↦ 0) (fun _ ↦ 0) 0
          (isDimensionFunctionCompatible_residueFieldSpecMap g s')
          (f.fiberToSpecResidueField (g s')) r (α (g s'))))

/-- Evaluating base change applies field-extension pullback and the fibre
identification. -/
theorem baseChange_apply {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} [LocallyOfFiniteType f]
    (hpb : IsPullback g' f' f g) {r : ℤ} (α : f.FiberCycleFamily r) (s' : S') :
    baseChange hpb α s' =
      CycleGroup.mapHom
        (fiberBaseChangeIso f g g' f' hpb s').hom
        ((pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0))
        (@Scheme.Hom.fiberRelativeDimensionFunction _ _ f'
          (MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance) s') r
        (CycleGroup.reindex
          ((pullback.snd (f.fiberToSpecResidueField (g s'))
              (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
            (fun _ ↦ 0))
          (add_zero r)
          (CycleGroup.baseChangePullback
            (Spec.map (g.residueFieldMap s')) (fun _ ↦ 0) (fun _ ↦ 0) 0
            (isDimensionFunctionCompatible_residueFieldSpecMap g s')
            (f.fiberToSpecResidueField (g s')) r (α (g s')))) := rfl

/-- Base change along the identity square is the identity on families. -/
theorem baseChange_id {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℤ} (α : f.FiberCycleFamily r) :
    baseChange (IsPullback.of_id_fst (f := f)) α = α := sorry

/-- Restriction of a family of fibre cycles to compatible opens `U ⊆ X` and
`V ⊆ S`. -/
noncomputable def restrict {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) {r : ℤ}
    (α : f.FiberCycleFamily r) : (f.resLE V U hU).FiberCycleFamily r :=
  fun s ↦
    CycleGroup.mapHom (resLEFiberIso f U V hU s).inv
      (((fiberOpen f U (V.ι s)).ι ≫
          f.fiberToSpecResidueField (V.ι s)).relativeDimensionFunction
        (fun _ ↦ 0))
      ((f.resLE V U hU).fiberRelativeDimensionFunction s) r
      (CycleGroup.Localization.openPullback
        (f.fiberToSpecResidueField (V.ι s)) (fun _ ↦ 0)
        (fiberOpen f U (V.ι s)) r (α (V.ι s)))

/-- Evaluating restriction applies open pullback on the fibre and the
restriction-fibre identification. -/
theorem restrict_apply {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V) {r : ℤ}
    (α : f.FiberCycleFamily r) (s : V.toScheme) :
    restrict U V hU α s =
      CycleGroup.mapHom (resLEFiberIso f U V hU s).inv
        (((fiberOpen f U (V.ι s)).ι ≫
            f.fiberToSpecResidueField (V.ι s)).relativeDimensionFunction
          (fun _ ↦ 0))
        ((f.resLE V U hU).fiberRelativeDimensionFunction s) r
        (CycleGroup.Localization.openPullback
          (f.fiberToSpecResidueField (V.ι s)) (fun _ ↦ 0)
          (fiberOpen f U (V.ι s)) r (α (V.ι s))) := rfl

/-- Flat pullback of a family of fibre cycles along a morphism of relative
dimension `e` over `S`. -/
noncomputable def flatPullback {X' X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {f' : X' ⟶ S}
     [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e] {r : ℤ}
    (α : f.FiberCycleFamily r) : f'.FiberCycleFamily (r + (e : ℤ)) :=
  fun s ↦
    fiberwiseFlatPullback s (f'.fiberToSpecResidueField s)
      (f.fiberToSpecResidueField s) (idTriangleFiberMap h hf s)
      (idTriangleFiberMap_fiberToSpecResidueField h hf s) e (α s)

/-- Evaluating flat pullback applies fibrewise flat pullback of the fibre map. -/
theorem flatPullback_apply {X' X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {f' : X' ⟶ S}
     [LocallyOfFiniteType f'] (h : X' ⟶ X)
    (hf : h ≫ f = f') (e : ℕ) [Flat h] [RelativeDimension h e] {r : ℤ}
    (α : f.FiberCycleFamily r) (s : S) :
    flatPullback h hf e α s =
      fiberwiseFlatPullback s (f'.fiberToSpecResidueField s)
        (f.fiberToSpecResidueField s) (idTriangleFiberMap h hf s)
        (idTriangleFiberMap_fiberToSpecResidueField h hf s) e (α s) := rfl

/-- Flat pullback along the identity, of relative dimension `0`, is reindexing
by `r + 0 = r`. -/
theorem flatPullback_id {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℤ} (α : f.FiberCycleFamily r) :
    flatPullback (𝟙 X) (Category.id_comp f) 0 α =
      reindex (add_zero r).symm α := sorry

/-- Proper pushforward of a family of fibre cycles along a morphism over `S`. -/
noncomputable def pushforward {X Y S : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] (h : X ⟶ Y)
    (hf : h ≫ fY = fX) [IsProper h] {r : ℤ} (α : fX.FiberCycleFamily r) :
    fY.FiberCycleFamily r :=
  fun s ↦
    fiberwisePushforward s (fX.fiberToSpecResidueField s)
      (fY.fiberToSpecResidueField s) (idTriangleFiberMap h hf s) (α s)

/-- Evaluating proper pushforward applies fibrewise pushforward of the fibre
map. -/
theorem pushforward_apply {X Y S : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
    [LocallyOfFiniteType fX] [LocallyOfFiniteType fY] (h : X ⟶ Y)
    (hf : h ≫ fY = fX) [IsProper h] {r : ℤ} (α : fX.FiberCycleFamily r) (s : S) :
    pushforward h hf α s =
      fiberwisePushforward s (fX.fiberToSpecResidueField s)
        (fY.fiberToSpecResidueField s) (idTriangleFiberMap h hf s) (α s) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Proper pushforward along the identity is the identity on families. -/
theorem pushforward_id {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℤ} (α : f.FiberCycleFamily r) :
    pushforward (𝟙 X) (Category.id_comp f) α = α := by
  funext s
  have hmap : idTriangleFiberMap (𝟙 X) (Category.id_comp f) s =
      𝟙 (f.fiber s) := by
    change pullback.map f (S.fromSpecResidueField s) f (S.fromSpecResidueField s)
      (𝟙 X) (AlgebraicGeometry.Spec.map (R := S.residueField s) (S := S.residueField s)
        (Scheme.Hom.residueFieldMap (𝟙 S) s)) (𝟙 S) (by simp) (by simp) =
          𝟙 (pullback f (S.fromSpecResidueField s))
    simp only [Scheme.residueFieldMap_id, AlgebraicGeometry.Spec.map_id]
    exact pullback.map_id (f := f) (g := S.fromSpecResidueField s)
  simp only [pushforward, fiberwisePushforward, hmap, CycleGroup.mapHom_id,
    AddMonoidHom.id_apply]

end AlgebraicGeometry.Scheme.Hom.FiberCycleFamily
