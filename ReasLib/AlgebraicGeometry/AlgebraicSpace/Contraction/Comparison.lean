/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementMap

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

namespace SolutionFor

variable {σ : ContractionSituation S} {X : AlgebraicSpace S}

/-- The morphism `U' ⟶ X \ T` obtained by transporting along `inverseImage` and
restricting `f`. -/
def openComplementIsoHom (sol : SolutionFor σ X) :
    σ.openComplement ⟶ openComplementAlong X sol.T :=
  eqToHom (congrArg (openComplementAlong σ.X') sol.inverseImage) ≫
    openComplementAlong.map sol.f sol.T

/-- `openComplementIsoHom` is transport along `inverseImage` followed by
restriction of `f`. -/
theorem openComplementIsoHom_eq (sol : SolutionFor σ X) :
    openComplementIsoHom sol =
      eqToHom (congrArg (openComplementAlong σ.X') sol.inverseImage) ≫
        openComplementAlong.map sol.f sol.T :=
  rfl

/-- A solution identifies `f⁻¹(X \ T)` with `X \ T`. -/
@[reducible] def isIso_openInverseImageTo (sol : SolutionFor σ X) :
    IsIso (openInverseImageTo sol.f (AlgebraicSpace.openComplementι X sol.T)) :=
  sol.isoOverOpen

/-- The inverse comparison `X \ T ⟶ U'` of the identification `U' ≅ X \ T`. -/
def openComplementIsoInv (sol : SolutionFor σ X) :
    openComplementAlong X sol.T ⟶ σ.openComplement :=
  inv (openInverseImageTo sol.f (AlgebraicSpace.openComplementι X sol.T))
      (I := sol.isIso_openInverseImageTo) ≫
    openInverseImageToOpenComplement sol.f sol.T ≫
    eqToHom (congrArg (openComplementAlong σ.X') sol.inverseImage.symm)

/-- `openComplementIsoInv` inverts `openInverseImageTo` and transports the
open inverse image into `U'`. -/
theorem openComplementIsoInv_eq (sol : SolutionFor σ X) :
    openComplementIsoInv sol =
      inv (openInverseImageTo sol.f (AlgebraicSpace.openComplementι X sol.T))
      (I := sol.isIso_openInverseImageTo) ≫
        openInverseImageToOpenComplement sol.f sol.T ≫
        eqToHom (congrArg (openComplementAlong σ.X') sol.inverseImage.symm) :=
  rfl

/-- `openComplementIsoHom` and `openComplementIsoInv` compose to the identity on
`U'`. -/
theorem openComplementIsoHom_inv_id (sol : SolutionFor σ X) :
    openComplementIsoHom sol ≫ openComplementIsoInv sol = 𝟙 σ.openComplement :=
  sorry

/-- `openComplementIsoInv` and `openComplementIsoHom` compose to the identity on
`X \ T`. -/
theorem openComplementIsoInv_hom_id (sol : SolutionFor σ X) :
    openComplementIsoInv sol ≫ openComplementIsoHom sol =
      𝟙 (openComplementAlong X sol.T) :=
  sorry

/-- The completion morphism induced by a solution and a scheme morphism is adic. -/
theorem tripleOfHom_isAdic (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    representableByAlgebraicSpaces (completionAlong.map x sol.T ≫ sol.a) :=
  sorry

/-- The open and completion morphisms induced by a solution are compatible. -/
theorem tripleOfHom_isCompatible (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    IsCompatible σ V (sol.T.preimage (Points.continuous_map x))
      (openComplementAlong.map x sol.T ≫ openComplementIsoInv sol)
      (completionAlong.map x sol.T ≫ sol.a) :=
  sorry

/-- The compatible triple associated to a morphism `x : V ⟶ X`. -/
def tripleOfHom (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) : Triple σ V where
  Z := sol.T.preimage (Points.continuous_map x)
  u' := openComplementAlong.map x sol.T ≫ openComplementIsoInv sol
  hatx := completionAlong.map x sol.T ≫ sol.a
  isAdic := tripleOfHom_isAdic sol x
  isCompatible := tripleOfHom_isCompatible sol x

/-- The closed subset of `tripleOfHom sol x` is the inverse image of `T`. -/
theorem tripleOfHom_Z (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (tripleOfHom sol x).Z = sol.T.preimage (Points.continuous_map x) :=
  rfl

/-- The open morphism of `tripleOfHom sol x` is the restriction of `x` followed
by the identification `X \ T ≅ U'`. -/
theorem tripleOfHom_u' (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (tripleOfHom sol x).u' =
      openComplementAlong.map x sol.T ≫ openComplementIsoInv sol :=
  rfl

/-- The completion morphism of `tripleOfHom sol x` is `a ∘ x_/Z`. -/
theorem tripleOfHom_hatx (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (tripleOfHom sol x).hatx = completionAlong.map x sol.T ≫ sol.a :=
  rfl

/-- `tripleOfHom` is natural in morphisms of locally Noetherian schemes over
`S`. -/
theorem tripleOfHom_map (sol : SolutionFor σ X) {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left] [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (x : ofOver V1 ⟶ X) :
    Triple.map φ (tripleOfHom sol x) = tripleOfHom sol (ofOverMap φ ≫ x) :=
  sorry


/-- The natural transformation `Mor_S(-, X) ⟶ F` with components `tripleOfHom`. -/
def ofHomNatTrans (sol : SolutionFor σ X) :
    homOnLocallyNoetherian X ⟶ σ.functor where
  app V := ofHom fun x ↦ tripleOfHom sol x
  naturality := by
    intro V1 V2 φ
    apply ConcreteCategory.hom_ext
    intro x
    exact (tripleOfHom_map sol φ.unop.hom x).symm

/-- Components of `ofHomNatTrans` are `tripleOfHom`. -/
theorem ofHomNatTrans_app (sol : SolutionFor σ X)
    (V : (locallyNoetherian S).FullSubcategory) (x : ofOver V.obj ⟶ X) :
    (ofHomNatTrans sol).app (op V) x = tripleOfHom sol x :=
  rfl


/-- A solution identifies its restricted functor of points with compatible triples. -/
theorem isIso_ofHomNatTrans (sol : SolutionFor σ X) :
    IsIso sol.ofHomNatTrans :=
  sorry

/-- The comparison `Mor_S(V, X) → F(V)` is bijective on each locally Noetherian
scheme `V` over `S`. -/
theorem tripleOfHom_bijective (sol : SolutionFor σ X)
    (V : (locallyNoetherian S).FullSubcategory) :
    Function.Bijective (fun x : ofOver V.obj ⟶ X ↦ sol.tripleOfHom x) :=
  sorry

end SolutionFor

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
