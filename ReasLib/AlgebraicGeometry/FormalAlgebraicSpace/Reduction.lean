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

end AlgebraicGeometry.FormalAlgebraicSpace
