module

public import stacks_project.Chap42.Lemma_42_35_4_Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u v w

namespace AlgebraicGeometry.BivariantClass

namespace OpenRestriction

/-- An open subscheme, regarded as a scheme over the same base. -/
abbrev over {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) : Over S :=
  Over.mk (U.ι ≫ X.hom)

/-- The underlying scheme of the open object is the canonical open subscheme. -/
theorem over_left {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) :
    (over X U).left = U := sorry

/-- An open subscheme of an `S`-scheme is locally of finite type over `S`. -/
instance instLocallyOfFiniteTypeOver
    {S : Scheme.{u}} (X : Over S) [LocallyOfFiniteType X.hom] (U : X.left.Opens) :
    LocallyOfFiniteType (over X U).hom := sorry

/-- The inclusion of an open subscheme as a morphism over the base. -/
def ι {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) : over X U ⟶ X :=
  Over.homMk U.ι

/-- The underlying scheme morphism of the open inclusion is the canonical inclusion. -/
theorem ι_left {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) :
    (ι X U).left = U.ι := sorry

/-- The inclusion of an open subscheme is locally of finite type. -/
instance instLocallyOfFiniteTypeι
    {S : Scheme.{u}} (X : Over S) (U : X.left.Opens) :
    LocallyOfFiniteType (ι X U).left := sorry

/-- The restriction of a morphism to compatible opens commutes with their structure maps. -/
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

/-- The pullback of an `S`-morphism, regarded as an `S`-scheme via its source projection. -/
abbrev baseChange
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) : Over S :=
  Over.mk (pullback.snd g.left f.left ≫ X.hom)

/-- The pullback of two locally finite-type `S`-schemes is locally of finite type over `S`. -/
instance instLocallyOfFiniteTypeBaseChange
    {S : Scheme.{u}} {X Y Y' : Over S}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y'.hom]
    (f : X ⟶ Y) (g : Y' ⟶ Y) : LocallyOfFiniteType (baseChange f g).hom := sorry

/-- The source projection from the canonical base change. -/
def baseChangeToSource
    {S : Scheme.{u}} {X Y Y' : Over S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    baseChange f g ⟶ X :=
  Over.homMk (pullback.snd g.left f.left)

/-- The target projection of the canonical base change commutes with structure maps. -/
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
      f.left g.left := sorry

/-- The comparison map from a test square for a component to the ambient pullback commutes. -/
theorem componentLift_comm
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    f'.left ≫ (g ≫ ι Y V).left = (i.left ≫ U.ι) ≫ f.left := sorry

/-- The underlying comparison map from a component test square to the ambient pullback. -/
def componentLiftLeft
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    X'.left ⟶ (baseChange f (g ≫ ι Y V)).left :=
  pullback.lift f'.left (i.left ≫ U.ι) (componentLift_comm f U V h i f' g square)

/-- The component comparison map respects the maps to the base scheme. -/
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
instance instFlatComponentLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    Flat (componentLift f U V h i f' g square).left := sorry

/-- The component comparison has relative dimension zero. -/
instance instRelativeDimensionComponentLift
    {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (U : X.left.Opens) (V : Y.left.Opens) (h : U ≤ f.left ⁻¹ᵁ V)
    {X' Y' : Over S} (i : X' ⟶ over X U) (f' : X' ⟶ Y')
    (g : Y' ⟶ over Y V)
    (square : IsPullback i.left f'.left (hom f U V h).left g.left) :
    Scheme.Hom.RelativeDimension (componentLift f U V h i f' g square).left 0 := sorry

/-- Flat pullback along a relative-dimension-zero component preserves the grading. -/
theorem componentDegree (k p : ℤ) : k - p + (0 : ℤ) = k - p := sorry

/-- Restriction of the cap family of a bivariant class to a compatible open component. -/
noncomputable def restrictCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CapFamily delta (hom f U V h) p :=
  fun {X' _} _ _ i f' g _ square k ↦
    (AddEquiv.toAddMonoidHom
      (@AddEquiv.cast ℤ (fun n : ℤ ↦ RelativeChow delta X' n) inferInstance
        (k - p + 0) (k - p) (componentDegree k p))).comp
      ((ChowGroup.flatPullback delta X' (baseChange f (g ≫ ι Y V))
        (componentLift f U V h i f' g square) 0 (k - p)).comp
        (c.cap (baseChangeToSource f (g ≫ ι Y V))
          (baseChangeToTarget f (g ≫ ι Y V)) (g ≫ ι Y V)
          (baseChange_isPullback f (g ≫ ι Y V)) k))

/-- Component restriction preserves compatibility with proper pushforward. -/
theorem restrictCap_map_proper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CompatibleWithProperPushforward delta
      (restrictCap delta f p U V h c) := sorry

/-- Component restriction preserves compatibility with flat pullback. -/
theorem restrictCap_pullback_flat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CompatibleWithFlatPullback delta
      (restrictCap delta f p U V h c) := sorry

/-- Component restriction preserves compatibility with effective-Cartier Gysin pullback. -/
theorem restrictCap_gysin_cartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c : BivariantClass delta f p) :
    CompatibleWithCartierGysin delta
      (restrictCap delta f p U V h c) := sorry

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
      gysin_cartier :=
        restrictCap_gysin_cartier delta f p U V h c }

/-- Restriction to one component sends zero to zero. -/
theorem restrict_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) :
    restrict delta f p U V h 0 = 0 := sorry

/-- Restriction to one component preserves addition. -/
theorem restrict_add
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) (U : X.left.Opens) (V : Y.left.Opens)
    (h : U ≤ f.left ⁻¹ᵁ V) (c d : BivariantClass delta f p) :
    restrict delta f p U V h (c + d) =
      restrict delta f p U V h c + restrict delta f p U V h d := sorry

/-- The homomorphism from a bivariant-class group to its compatible open components. -/
noncomputable def components
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i)) :
    BivariantClass delta f p →+
      ∀ i, BivariantClass delta
        (hom f (U i) (V (a i)) (h i)) p where
  toFun c i := restrict delta f p (U i) (V (a i)) (h i) c
  map_zero' := sorry
  map_add' := sorry

/-- Evaluation of component restriction is restriction to the selected component. -/
theorem components_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X Y : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (p : ℤ) {I : Type v} {J : Type w}
    (U : I → X.left.Opens) (V : J → Y.left.Opens) (a : I → J)
    (h : ∀ i, U i ≤ f.left ⁻¹ᵁ V (a i))
    (c : BivariantClass delta f p) (i : I) :
    components delta f p U V a h c i =
      restrict delta f p (U i) (V (a i)) (h i) c := sorry

end OpenRestriction

end AlgebraicGeometry.BivariantClass

