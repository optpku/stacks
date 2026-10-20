module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback

/-!
# Reductions of formal algebraic spaces

`ReductionData X` records the reduced algebraic space mapping by a
representable thickening into a formal algebraic space, together with its
universal factorization property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A reduced algebraic-space presentation of a formal algebraic space. -/
structure ReductionData {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] where
  /-- The underlying reduced algebraic space. -/
  space : AlgebraicSpace S
  /-- The structure morphism from the reduced space to `X`. -/
  ι : space.functorOfPoints ⟶ X
  /-- The reduction is reduced in the étale-local sense. -/
  isReduced : AlgebraicSpace.existsSurjectiveEtale
    (IsReduced : ObjectProperty Scheme.{u}) space
  /-- The structure morphism is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces ι
  /-- Every Yoneda pullback is a closed immersion and induces a surjection on points. -/
  isThickening : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
    AlgebraicSpace.IsClosedImmersion
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ) ∧
      Function.Surjective
        (AlgebraicSpace.Points.map
          (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ))
  /-- Maps from reduced algebraic spaces factor uniquely through the reduction. -/
  liftUnique {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X) :
    ∃! h : U.functorOfPoints ⟶ space.functorOfPoints, h ≫ ι = g

/-- The factor through a reduction selected by its universal property. -/
noncomputable def ReductionData.mapFromReduced {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] (R : ReductionData X)
    {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X) :
    U.functorOfPoints ⟶ R.space.functorOfPoints :=
  Classical.choose (R.liftUnique hU g)

/-- The selected factor through a reduction satisfies its factorization and uniqueness laws. -/
theorem ReductionData.mapFromReduced_spec {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] (R : ReductionData X)
    {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.existsSurjectiveEtale
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X) :
    ReductionData.mapFromReduced R hU g ≫ R.ι = g ∧
      ∀ h : U.functorOfPoints ⟶ R.space.functorOfPoints,
        h ≫ R.ι = g → h = ReductionData.mapFromReduced R hU g := by
  have h := Classical.choose_spec (R.liftUnique hU g)
  exact ⟨h.1, fun h' hh' ↦ h.2 h' hh'⟩

/-- The morphism between reductions induced by a morphism of formal algebraic spaces. -/
def ReductionData.map {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    RX.space ⟶ RY.space :=
  RY.mapFromReduced RX.isReduced (RX.ι ≫ f)

/-- The induced morphism of reductions commutes with the reduction inclusions. -/
theorem ReductionData.map_spec {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    NatTrans.vcomp (RX.map RY f) RY.ι = RX.ι ≫ f :=
  (RY.mapFromReduced_spec RX.isReduced (RX.ι ≫ f)).1

/-- A morphism of reductions commuting with their inclusions is the induced morphism. -/
theorem ReductionData.map_unique {S : Scheme.{u}}
    {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y)
    {g : RX.space ⟶ RY.space} (hg : NatTrans.vcomp g RY.ι = RX.ι ≫ f) :
    g = RX.map RY f :=
  (RY.mapFromReduced_spec RX.isReduced (RX.ι ≫ f)).2 g hg

/-- The induced morphism on a reduction preserves the identity morphism. -/
theorem ReductionData.map_id {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (RX : ReductionData X) :
    RX.map RX (𝟙 X) = 𝟙 RX.space :=
  sorry

/-- The induced morphisms on reductions preserve composition. -/
theorem ReductionData.map_comp {S : Scheme.{u}}
    {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    (RX : ReductionData X) (RY : ReductionData Y) (RZ : ReductionData Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    RX.map RZ (f ≫ g) = RX.map RY f ≫ RY.map RZ g := by
  symm
  apply map_unique RX RZ (f ≫ g)
  change NatTrans.vcomp (NatTrans.vcomp (RX.map RY f) (RY.map RZ g)) RZ.ι = _
  calc
    _ = NatTrans.vcomp (RX.map RY f) (NatTrans.vcomp (RY.map RZ g) RZ.ι) :=
      Category.assoc (obj := (Over S)ᵒᵖ ⥤ Type u) _ _ _
    _ = NatTrans.vcomp (RX.map RY f) (RY.ι ≫ g) := by rw [map_spec]
    _ = NatTrans.vcomp (NatTrans.vcomp (RX.map RY f) RY.ι) g :=
      (Category.assoc (obj := (Over S)ᵒᵖ ⥤ Type u) _ _ _).symm
    _ = (RX.ι ≫ f) ≫ g := by
      rw [map_spec]
      rfl
    _ = RX.ι ≫ (f ≫ g) := Category.assoc _ _ _

end AlgebraicGeometry.FormalAlgebraicSpace
