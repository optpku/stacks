module

public import ReasLib.AlgebraicGeometry.BivariantClass.Cospan

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Cospan

/-- The two composites defining the pullback of a proper morphism along an
identity-leg pullback agree. -/
theorem properBaseChangeMap_comm
    {S : Scheme.{u}} {X₁ X₂ Z' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    (iY.left ≫ f.left) ≫ (𝟙 X₁ : X₁ ⟶ X₁).left = qY.left ≫ g.left := sorry

/-- The displayed base-change comparison respects the maps to the base scheme. -/
theorem properBaseChangeMap_over
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    squareX.lift (iY.left ≫ f.left) qY.left
        (properBaseChangeMap_comm f g iY qY squareY) ≫ X'.hom = Y'.hom := sorry

/-- The base-changed map from the pullback of `f` to a displayed pullback of the
identity of its target. -/
def properBaseChangeMap
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) : Y' ⟶ X' :=
  Over.homMk
    (squareX.lift (iY.left ≫ f.left) qY.left (properBaseChangeMap_comm f g iY qY squareY))
    (properBaseChangeMap_over f g iX qX squareX iY qY squareY)

/-- The base-changed proper map has the expected projection to the source of the
identity leg. -/
theorem properBaseChangeMap_fst
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    (properBaseChangeMap f g iX qX squareX iY qY squareY).left ≫ iX.left =
      iY.left ≫ f.left := sorry

/-- The base-changed proper map has the expected projection to the varying middle
scheme. -/
theorem properBaseChangeMap_snd
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) (g : Z' ⟶ X₁)
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    (properBaseChangeMap f g iX qX squareX iY qY squareY).left ≫ qX.left = qY.left := sorry

/-- A displayed base change of a proper morphism along an identity-leg pullback is
proper. -/
instance properBaseChangeMapIsProper
    {S : Scheme.{u}} {X₁ X₂ Z' X' Y' : Over S} (f : X₂ ⟶ X₁) [IsProper f.left]
    (g : Z' ⟶ X₁) (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) :
    IsProper (properBaseChangeMap f g iX qX squareX iY qY squareY).left := sorry

/-- Reindex a relative Chow group along an equality of grading indices. -/
def castDegree
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {T : Over S} [LocallyOfFiniteType T.hom] {m n : ℤ} (h : m = n) :
    RelativeChow delta T m →+ RelativeChow delta T n :=
  h ▸ AddMonoidHom.id (RelativeChow delta T m)

/-- Reindexing by a degree equality sends each Chow class to its transported value. -/
theorem castDegree_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {T : Over S} [LocallyOfFiniteType T.hom] {m n : ℤ} (h : m = n)
    (alpha : RelativeChow delta T m) : castDegree delta h alpha = h ▸ alpha := sorry

/-- The cap family given by proper pushforward along the displayed base change of a
proper morphism. -/
def properPushforwardCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] : CapFamily delta (𝟙 X₁) f 0 :=
  fun {_ X' Y'} _ _ _ g _ iX qX squareX iY _ qY squareY k ↦
    (castDegree delta (Int.sub_zero k).symm).comp
      (ChowGroup.map delta Y' X'
        (properBaseChangeMap f g iX qX squareX iY qY squareY) k)

/-- Evaluation of the proper-pushforward cap family is Chow pushforward along the
displayed base-change map, followed by the degree-zero transport. -/
theorem properPushforwardCap_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ Z' X' Y' : Over S}
    [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] (g : Z' ⟶ X₁) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) (k : ℤ) :
    properPushforwardCap delta f g iX qX squareX iY qY squareY k =
      (castDegree delta (Int.sub_zero k).symm).comp
        (ChowGroup.map delta Y' X'
          (properBaseChangeMap f g iX qX squareX iY qY squareY) k) := sorry

/-- Proper pushforward cap maps satisfy proper-pushforward compatibility. -/
theorem properPushforwardCap_mapProper
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] :
    CompatibleWithProperPushforward delta (properPushforwardCap delta f) := sorry

/-- Proper pushforward cap maps satisfy fixed-relative-dimension flat-pullback
compatibility. -/
theorem properPushforwardCap_pullbackFlat
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] :
    CompatibleWithFlatPullback delta (properPushforwardCap delta f) := sorry

/-- Proper pushforward cap maps satisfy effective-Cartier Gysin compatibility. -/
theorem properPushforwardCap_gysinCartier
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] :
    CompatibleWithCartierGysin delta (properPushforwardCap delta f) := sorry

/-- A proper morphism `f : X₂ ⟶ X₁` defines a degree-zero bivariant cospan
operation on `X₁ ⟶ X₁ ⟵ X₂` by proper pushforward after every base change. -/
def properPushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ : Over S} [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] : Cospan delta (𝟙 X₁) f 0 where
  cap := properPushforwardCap delta f
  map_proper := properPushforwardCap_mapProper delta f
  pullback_flat := properPushforwardCap_pullbackFlat delta f
  gysin_cartier := properPushforwardCap_gysinCartier delta f

/-- Evaluation of the proper cospan class is Chow pushforward along the displayed
base-change map. -/
theorem properPushforward_cap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    {X₁ X₂ Z' X' Y' : Over S}
    [LocallyOfFiniteType X₁.hom] [LocallyOfFiniteType X₂.hom]
    [LocallyOfFiniteType Z'.hom] [LocallyOfFiniteType X'.hom]
    [LocallyOfFiniteType Y'.hom]
    (f : X₂ ⟶ X₁) [IsProper f.left] (g : Z' ⟶ X₁) [LocallyOfFiniteType g.left]
    (iX : X' ⟶ X₁) (qX : X' ⟶ Z')
    (squareX : IsPullback iX.left qX.left (𝟙 X₁ : X₁ ⟶ X₁).left g.left)
    (iY : Y' ⟶ X₂) [LocallyOfFiniteType iY.left] (qY : Y' ⟶ Z')
    (squareY : IsPullback iY.left qY.left f.left g.left) (k : ℤ) :
    (properPushforward delta f).cap g iX qX squareX iY qY squareY k =
      (castDegree delta (Int.sub_zero k).symm).comp
        (ChowGroup.map delta Y' X'
          (properBaseChangeMap f g iX qX squareX iY qY squareY) k) := sorry

end AlgebraicGeometry.BivariantClass.Cospan
