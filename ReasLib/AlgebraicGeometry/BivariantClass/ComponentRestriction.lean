/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.BivariantClass.ComponentRestriction

/-- An open subscheme, regarded as a scheme over the same base. -/
abbrev over {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) : Over S :=
  Over.mk (U.ι ≫ X.hom)

/-- The underlying scheme of an open object is its canonical open subscheme. -/
theorem over_left {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) :
    (over X U).left = U := sorry

/-- An open subscheme of an `S`-scheme is locally of finite type over `S`. -/
theorem locallyOfFiniteTypeOver
    {S : Scheme.{u}} (X : Over S) [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    LocallyOfFiniteType (over X U).hom := sorry

/-- The inclusion of an open subscheme as a morphism over the base. -/
def ι {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) : over X U ⟶ X :=
  Over.homMk U.ι

/-- The underlying scheme morphism of the open inclusion is the canonical inclusion. -/
theorem ι_left {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) :
    (ι X U).left = U.ι := sorry

/-- The inclusion of an open subscheme is locally of finite type. -/
theorem locallyOfFiniteTypeι
    {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) :
    LocallyOfFiniteType (ι X U).left := sorry

/-- Restriction of a morphism to compatible opens commutes with the structure maps. -/
theorem hom_over
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V) :
    f.left.resLE V U h ≫ (over Y V).hom = (over X U).hom := sorry

/-- The restriction of a morphism of `S`-schemes to compatible open subschemes. -/
def hom
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V) :
    over X U ⟶ over Y V :=
  Over.homMk (f.left.resLE V U h) (hom_over f U V h)

/-- The underlying scheme morphism of an open restriction is the canonical restriction. -/
theorem hom_left
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V) :
    (hom f U V h).left = f.left.resLE V U h := sorry

/-- The pullback of an `S`-morphism, regarded as an `S`-scheme through its source. -/
abbrev baseChange
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) : Over S :=
  Over.mk (pullback.snd g.left f.left ≫ X.hom)

/-- The pullback of locally finite-type `S`-schemes is locally of finite type over `S`. -/
theorem locallyOfFiniteTypeBaseChange
    {S : Scheme.{u}} {X Y Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (g : Y' ⟶ Y) : LocallyOfFiniteType (baseChange f g).hom := sorry

/-- The source projection from the canonical base change. -/
def baseChangeToSource
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    baseChange f g ⟶ X :=
  Over.homMk (pullback.snd g.left f.left)

/-- The target projection of a canonical base change commutes with structure maps. -/
theorem baseChangeToTarget_over
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    pullback.fst g.left f.left ≫ Y'.hom = (baseChange f g).hom := sorry

/-- The target projection from the canonical base change. -/
def baseChangeToTarget
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    baseChange f g ⟶ Y' :=
  Over.homMk (pullback.fst g.left f.left) (baseChangeToTarget_over f g)

/-- The canonical base-change square is cartesian. -/
theorem baseChange_isPullback
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    IsPullback (baseChangeToSource f g).left (baseChangeToTarget f g).left
      f.left g.left := by
  change IsPullback (pullback.snd g.left f.left) (pullback.fst g.left f.left)
    f.left g.left
  exact (IsPullback.of_hasPullback g.left f.left).flip

/-- The comparison from a component test square to the ambient pullback commutes. -/
theorem componentLift_comm
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    f'.left ≫ (g ≫ ι Y V).left = (i.left ≫ U.ι) ≫ f.left := sorry

/-- The underlying comparison map from a component square to the ambient pullback. -/
def componentLiftLeft
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    X'.left ⟶ (baseChange f (g ≫ ι Y V)).left :=
  pullback.lift f'.left (i.left ≫ U.ι) (componentLift_comm f U V h i f' g square)

/-- The component comparison respects the maps to the base scheme. -/
theorem componentLift_over
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    componentLiftLeft f U V h i f' g square ≫
      (baseChange f (g ≫ ι Y V)).hom = X'.hom := sorry

/-- The comparison from a component test square to the ambient pullback. -/
def componentLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    X' ⟶ baseChange f (g ≫ ι Y V) :=
  Over.homMk (componentLiftLeft f U V h i f' g square)
    (componentLift_over f U V h i f' g square)

/-- The component comparison is flat. -/
theorem flatComponentLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    Flat (componentLift f U V h i f' g square).left := sorry

/-- The component comparison has relative dimension zero. -/
theorem relativeDimensionComponentLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    Scheme.Hom.RelativeDimension (componentLift f U V h i f' g square).left 0 := sorry

/-- Pullback along a relative-dimension-zero component preserves the grading. -/
theorem componentDegree (k p : ℤ) : k - p + (0 : ℤ) = k - p := sorry

/-- Restriction of a cap family to a compatible open component. -/
noncomputable def restrictCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    @CapFamily S inferInstance delta inferInstance (over X U) (over Y V)
      (locallyOfFiniteTypeOver X U) (locallyOfFiniteTypeOver Y V) (hom f U V h) p :=
  fun {X' Y' : Over S}
      [LocallyOfFiniteType X'.hom] [LocallyOfFiniteType Y'.hom]
      (i : X' ⟶ over X U) (f' : X' ⟶ Y') (g : Y' ⟶ over Y V)
      [LocallyOfFiniteType g.left]
      (square : IsPullback i.left f'.left (hom f U V h).left g.left) (k : ℤ) ↦
    -- Local instance justification (proof-local temporary data): the ambient cap map requires this finite-type proof for the open inclusion.
    letI : LocallyOfFiniteType (ι Y V).left := locallyOfFiniteTypeι Y V
    -- Local instance justification (proof-local temporary data): the ambient cap map requires this finite-type proof for the base-change object.
    letI : LocallyOfFiniteType (baseChange f (g ≫ ι Y V)).hom :=
      locallyOfFiniteTypeBaseChange f (g ≫ ι Y V)
    -- Local instance justification (proof-local temporary data): `flatPullback` requires this flatness proof for the component comparison.
    letI : Flat
        (componentLift (f := f) (U := U) (V := V) (h := h)
          (X' := X') (Y' := Y') (i := i) (f' := f') (g := g) (square := square)).left :=
      flatComponentLift (f := f) (U := U) (V := V) (h := h)
        (X' := X') (Y' := Y') (i := i) (f' := f') (g := g) (square := square)
    -- Local instance justification (proof-local temporary data): `flatPullback` requires this relative-dimension proof for the component comparison.
    letI : Scheme.Hom.RelativeDimension
        (componentLift (f := f) (U := U) (V := V) (h := h)
          (X' := X') (Y' := Y') (i := i) (f' := f') (g := g) (square := square)).left 0 :=
      relativeDimensionComponentLift (f := f) (U := U) (V := V) (h := h)
        (X' := X') (Y' := Y') (i := i) (f' := f') (g := g) (square := square)
    (AddEquiv.toAddMonoidHom
      (@AddEquiv.cast ℤ
        (fun n : ℤ ↦ RelativeChow (S := S) (delta := delta) (X := X') (k := n))
        inferInstance
        (k - p + 0) (k - p) (componentDegree (k := k) (p := p)))).comp
      ((ChowGroup.flatPullback (S := S) (δ := delta) (X := X')
        (Y := baseChange f (g ≫ ι Y V))
        (f := componentLift (f := f) (U := U) (V := V) (h := h)
          (X' := X') (Y' := Y') (i := i) (f' := f') (g := g) (square := square))
        (r := 0) (k := k - p)).comp
        (c.cap (i := baseChangeToSource f (g ≫ ι Y V))
          (f' := baseChangeToTarget f (g ≫ ι Y V)) (g := g ≫ ι Y V)
          (baseChange_isPullback f (g ≫ ι Y V)) k))

/-- Component restriction preserves proper pushforward. -/
theorem restrictCap_map_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CompatibleWithProperPushforward delta (restrictCap delta f p U V h c) := sorry

/-- Component restriction preserves flat pullback. -/
theorem restrictCap_pullback_flat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CompatibleWithFlatPullback delta (restrictCap delta f p U V h c) := sorry

/-- Component restriction preserves effective-Cartier Gysin pullback. -/
theorem restrictCap_gysin_cartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CompatibleWithCartierGysin delta (restrictCap delta f p U V h c) := sorry

/-- Restriction of a bivariant class to one compatible open component. -/
noncomputable def restrict
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) :
    BivariantClass delta f p → BivariantClass delta (hom f U V h) p :=
  fun c ↦
    { cap := restrictCap delta f p U V h c
      map_proper := restrictCap_map_proper delta f p U V h c
      pullback_flat := restrictCap_pullback_flat delta f p U V h c
      gysin_cartier := restrictCap_gysin_cartier delta f p U V h c }

/-- Restriction to one component sends the pointwise-zero class to zero. -/
theorem restrict_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) :
    restrict delta f p U V h (pointwiseZero delta f p) =
      pointwiseZero delta (hom f U V h) p := sorry

/-- Restriction to one component preserves pointwise addition. -/
theorem restrict_add
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c d : BivariantClass delta f p) :
    restrict delta f p U V h (pointwiseAdd delta f p c d) =
      pointwiseAdd delta (hom f U V h) p
        (restrict delta f p U V h c) (restrict delta f p U V h d) := sorry

/-- The additive homomorphism from a bivariant-class group to its open components. -/
noncomputable def components
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    @AddMonoidHom
      (BivariantClass delta f p)
      (∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p)
      { zero := pointwiseZero delta f p
        add := pointwiseAdd delta f p }
      { zero := fun i ↦ pointwiseZero delta (hom f (U i) (V (a i)) (h i)) p
        add := fun c d i ↦
          pointwiseAdd delta (hom f (U i) (V (a i)) (h i)) p (c i) (d i) } :=
  let sourceGroup := pointwiseAddCommGroup delta f p
  let sourceMonoid := @AddCommMonoid.toAddMonoid _
    (@AddCommGroup.toAddCommMonoid _ sourceGroup)
  let sourceAddZero := @AddZeroClass.toAddZero _
    (@AddMonoid.toAddZeroClass _ sourceMonoid)
  let targetGroup :
      AddCommGroup (∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p) :=
    @Pi.addCommGroup I
      (fun i ↦ BivariantClass delta (hom f (U i) (V (a i)) (h i)) p)
      (fun i ↦
        @pointwiseAddCommGroup S inferInstance delta inferInstance
          (over X (U i)) (over Y (V (a i)))
          (locallyOfFiniteTypeOver X (U i)) (locallyOfFiniteTypeOver Y (V (a i)))
          (hom f (U i) (V (a i)) (h i)) p)
  let targetMonoid := @AddCommMonoid.toAddMonoid _
    (@AddCommGroup.toAddCommMonoid _ targetGroup)
  let targetAddZero := @AddZeroClass.toAddZero _
    (@AddMonoid.toAddZeroClass _ targetMonoid)
  -- Local instance justification (defeq pin): structure syntax must use the explicit source additive data in the result type.
  letI : AddZero (BivariantClass delta f p) := sourceAddZero
  -- Local instance justification (defeq pin): structure syntax must use the explicit componentwise additive data in the result type.
  letI : AddZero (∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p) :=
    targetAddZero
  { toFun := fun c i ↦ restrict delta f p (U i) (V (a i)) (h i) c
    map_zero' := sorry
    map_add' := sorry }

/-- Evaluation of the component map is restriction to the selected component. -/
theorem components_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : BivariantClass delta f p) (i : I) :
    components delta f p U V a h c i =
      restrict delta f p (U i) (V (a i)) (h i) c := sorry

/-- Assemble the cap maps of bivariant classes on compatible disjoint clopen components. -/
noncomputable def assembleCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : ∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p) :
    CapFamily delta f p :=
  fun {X' Y'} _ _ ιX f' g _ square k ↦
    { toFun := fun alpha ↦
        let sourceOpen : I → X'.left.Opens := fun q ↦ ιX.left ⁻¹ᵁ U q
        let targetOpen : I → Y'.left.Opens := fun q ↦ g.left ⁻¹ᵁ V (a q)
        let componentCycle : I →
            CycleGroup X'.left (X'.hom.relativeDimensionFunction delta) (k - p) :=
          fun q ↦
            let hRestricted : sourceOpen q ≤ f'.left ⁻¹ᵁ targetOpen q := sorry
            -- Local instance justification (proof-local temporary data): the cap map is evaluated on the source open as an object locally of finite type over the base.
            letI : LocallyOfFiniteType (over X' (sourceOpen q)).hom :=
              locallyOfFiniteTypeOver X' (sourceOpen q)
            -- Local instance justification (proof-local temporary data): the cap map is evaluated on the target open as an object locally of finite type over the base.
            letI : LocallyOfFiniteType (over Y' (targetOpen q)).hom :=
              locallyOfFiniteTypeOver Y' (targetOpen q)
            -- Local instance justification (proof-local temporary data): restriction of the test morphism to the selected target component is locally of finite type.
            letI : LocallyOfFiniteType
                (hom g (targetOpen q) (V (a q)) le_rfl).left := sorry
            -- Local instance justification (proof-local temporary data): the clopen source inclusion is quasicompact, so its cycle can be extended by zero.
            letI : QuasiCompact (sourceOpen q).ι := sorry
            -- Local instance justification (proof-local temporary data): an open immersion is flat.
            letI : Flat (ι Y' (targetOpen q)).left := sorry
            -- Local instance justification (proof-local temporary data): a clopen immersion has relative dimension zero.
            letI : Scheme.Hom.RelativeDimension (ι Y' (targetOpen q)).left 0 := sorry
            CycleGroup.mapHom (sourceOpen q).ι
              ((over X' (sourceOpen q)).hom.relativeDimensionFunction delta)
              (X'.hom.relativeDimensionFunction delta) (k - p)
              ((c q).cap
                (hom ιX (sourceOpen q) (U q) le_rfl)
                (hom f' (sourceOpen q) (targetOpen q) hRestricted)
                (hom g (targetOpen q) (V (a q)) le_rfl) sorry k
                ((@AddEquiv.cast ℤ
                    (fun n : ℤ ↦ RelativeChow delta (over Y' (targetOpen q)) n)
                    inferInstance (k + (0 : ℤ)) k (add_zero k)).toAddMonoidHom
                  (ChowGroup.flatPullback delta (over Y' (targetOpen q)) Y'
                    (ι Y' (targetOpen q)) 0 k alpha))).out
        @chowClass X'.left (LocallyOfFiniteType.isLocallyNoetherian X'.hom)
          (X'.hom.relativeDimensionFunction delta) inferInstance (k - p)
          (CycleGroup.locallyFiniteSum (X'.hom.relativeDimensionFunction delta) (k - p)
            componentCycle sorry)
      map_zero' := sorry
      map_add' := sorry }

/-- Assemble compatible componentwise bivariant classes into a global bivariant class. -/
noncomputable def assemble
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    @AddMonoidHom
      (∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p)
      (BivariantClass delta f p)
      { zero := fun i ↦ pointwiseZero delta (hom f (U i) (V (a i)) (h i)) p
        add := fun c d i ↦
          pointwiseAdd delta (hom f (U i) (V (a i)) (h i)) p (c i) (d i) }
      { zero := pointwiseZero delta f p
        add := pointwiseAdd delta f p } :=
  let sourceGroup :
      AddCommGroup (∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p) :=
    @Pi.addCommGroup I
      (fun i ↦ BivariantClass delta (hom f (U i) (V (a i)) (h i)) p)
      (fun i ↦
        @pointwiseAddCommGroup S inferInstance delta inferInstance
          (over X (U i)) (over Y (V (a i)))
          (locallyOfFiniteTypeOver X (U i)) (locallyOfFiniteTypeOver Y (V (a i)))
          (hom f (U i) (V (a i)) (h i)) p)
  let sourceMonoid := @AddCommMonoid.toAddMonoid _
    (@AddCommGroup.toAddCommMonoid _ sourceGroup)
  let sourceAddZero := @AddZeroClass.toAddZero _
    (@AddMonoid.toAddZeroClass _ sourceMonoid)
  let targetGroup := pointwiseAddCommGroup delta f p
  let targetMonoid := @AddCommMonoid.toAddMonoid _
    (@AddCommGroup.toAddCommMonoid _ targetGroup)
  let targetAddZero := @AddZeroClass.toAddZero _
    (@AddMonoid.toAddZeroClass _ targetMonoid)
  -- Local instance justification (defeq pin): structure syntax must use the explicit componentwise additive data in the domain.
  letI : AddZero (∀ i, BivariantClass delta (hom f (U i) (V (a i)) (h i)) p) :=
    sourceAddZero
  -- Local instance justification (defeq pin): structure syntax must use the explicit global additive data in the codomain.
  letI : AddZero (BivariantClass delta f p) := targetAddZero
  { toFun := fun c ↦
      { cap := assembleCap delta f p U V a hU_cover hV_cover hU_disjoint
          hV_disjoint hU_clopen hV_clopen h c
        map_proper := sorry
        pullback_flat := sorry
        gysin_cartier := sorry }
    map_zero' := sorry
    map_add' := sorry }

/-- Compatible disjoint clopen decompositions identify a bivariant class with its
component restrictions. -/
theorem components_bijective
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (hU_cover : iSup U = ⊤) (hV_cover : iSup V = ⊤)
    (hU_disjoint : Pairwise (fun i j ↦ Disjoint (U i : Set X.left) (U j : Set X.left)))
    (hV_disjoint : Pairwise (fun i j ↦ Disjoint (V i : Set Y.left) (V j : Set Y.left)))
    (hU_clopen : ∀ i, IsClopen (U i : Set X.left))
    (hV_clopen : ∀ j, IsClopen (V j : Set Y.left))
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    Function.Bijective (components delta f p U V a h) := sorry

/-- Compatible restrictions of composable morphisms compose to the restriction of
their composite. -/
theorem hom_comp
    {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (U : X.left.Opens) (V : Y.left.Opens) (W : Z.left.Opens)
    (hf : U ≤ f.left ⁻¹ᵁ V) (hg : V ≤ g.left ⁻¹ᵁ W)
    (hfg : U ≤ (f ≫ g).left ⁻¹ᵁ W) :
    hom f U V hf ≫ hom g V W hg = hom (f ≫ g) U W hfg := sorry

end AlgebraicGeometry.BivariantClass.ComponentRestriction
