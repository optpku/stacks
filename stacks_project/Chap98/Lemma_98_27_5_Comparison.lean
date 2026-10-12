/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap98.Lemma_98_27_6_Solution

/-!
# Comparison of contraction solutions with restricted functor of points

A solution `(f : X' ⟶ X, T, a)` induces the explicit map sending a morphism
`x : V ⟶ X` to the compatible triple `(Z, u', hatx)`, packaged as a natural
transformation `homOnLocallyNoetherian X ⟶ σ.functor`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty Opposite
open CategoryTheory.Limits TopologicalSpace TypeCat
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison from the open inverse image of `X \ T` along `f` to the open
complement of the closed preimage on `X'`. -/
def openInverseImageToOpenComplement {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    (f : X' ⟶ X) (T : Closeds (Points X)) :
    openInverseImage f (openComplementι X T) ⟶
      openComplementAlong X' (T.preimage (Points.continuous_map f)) where
  app U := ofHom fun p ↦
    ⟨(openInverseImageι f (openComplementι X T)).app U p, sorry⟩
  naturality := sorry

/-- Postcomposing `openInverseImageToOpenComplement` with the open-complement
inclusion recovers `openInverseImageι`. -/
theorem openInverseImageToOpenComplement_comp_ι {S : Scheme.{u}}
    {X' X : AlgebraicSpace S} (f : X' ⟶ X) (T : Closeds (Points X)) :
    openInverseImageToOpenComplement f T ≫
        openComplementι X' (T.preimage (Points.continuous_map f)) =
      openInverseImageι f (openComplementι X T) :=
  sorry

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

namespace SolutionFor

variable {σ : ContractionSituation S} {X : AlgebraicSpace S}
  [LocallyOfFiniteType (toBase X)]

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
  sorry

/-- A solution identifies `f⁻¹(X \ T)` with `X \ T`. -/
instance instIsIso_openInverseImageTo (sol : SolutionFor σ X) :
    IsIso (openInverseImageTo sol.f (AlgebraicSpace.openComplementι X sol.T)) :=
  sol.isoOverOpen

/-- The inverse comparison `X \ T ⟶ U'` of the identification `U' ≅ X \ T`. -/
def openComplementIsoInv (sol : SolutionFor σ X) :
    openComplementAlong X sol.T ⟶ σ.openComplement :=
  inv (openInverseImageTo sol.f (AlgebraicSpace.openComplementι X sol.T)) ≫
    openInverseImageToOpenComplement sol.f sol.T ≫
    eqToHom (congrArg (openComplementAlong σ.X') sol.inverseImage.symm)

/-- `openComplementIsoInv` inverts `openInverseImageTo` and transports the
open inverse image into `U'`. -/
theorem openComplementIsoInv_eq (sol : SolutionFor σ X) :
    openComplementIsoInv sol =
      inv (openInverseImageTo sol.f (AlgebraicSpace.openComplementι X sol.T)) ≫
        openInverseImageToOpenComplement sol.f sol.T ≫
        eqToHom (congrArg (openComplementAlong σ.X') sol.inverseImage.symm) :=
  sorry

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

/-- The open complement of the inverse image of `T` and the restriction of `x`
to `U'` agree after composing to `X`. -/
theorem tripleOfHom_openToV'_comm (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    AlgebraicSpace.openComplementι (ofOver V) (sol.T.preimage (Points.continuous_map x)) ≫ x =
      (openComplementAlong.map x sol.T ≫
          openComplementIsoInv sol ≫ σ.openComplementι) ≫
        sol.f :=
  sorry

/-- The map from `V \ Z` into the fibre product `V ×_X X'`. -/
def tripleOfHom_openToV' (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    openComplementAlong (ofOver V) (sol.T.preimage (Points.continuous_map x)) ⟶
      pullback x sol.f :=
  pullback.lift
    (AlgebraicSpace.openComplementι (ofOver V) (sol.T.preimage (Points.continuous_map x)))
    (openComplementAlong.map x sol.T ≫ openComplementIsoInv sol ≫ σ.openComplementι)
    (tripleOfHom_openToV'_comm sol x)

/-- The inverse image of `Z` along `V' ⟶ V` agrees with the inverse image of
`T'` along `V' ⟶ X'`. -/
theorem tripleOfHom_preimage_fst (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (sol.T.preimage (Points.continuous_map x)).preimage
        (Points.continuous_map (pullback.fst x sol.f)) =
      σ.T'.preimage (Points.continuous_map (pullback.snd x sol.f)) :=
  sorry

/-- The completion of the projection `x' : V' ⟶ X'` along `Z`. -/
def tripleOfHom_hatx' (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    completionAlong (pullback x sol.f)
        ((sol.T.preimage (Points.continuous_map x)).preimage
          (Points.continuous_map (pullback.fst x sol.f))) ⟶
      σ.completion :=
  completionAlong.congrClosed (tripleOfHom_preimage_fst sol x) ≫
    completionAlong.map (pullback.snd x sol.f) σ.T'

/-- The compatible triple associated to a morphism `x : V ⟶ X`. -/
def tripleOfHom (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) : Triple σ V where
  Z := sol.T.preimage (Points.continuous_map x)
  u' := openComplementAlong.map x sol.T ≫ openComplementIsoInv sol
  hatx := completionAlong.map x sol.T ≫ sol.a
  isAdic := sorry
  isCompatible :=
    ⟨CompatibilityWitness.of (pullback x sol.f) (pullback.fst x sol.f)
      (tripleOfHom_openToV' sol x) (tripleOfHom_hatx' sol x)
      (pullback.snd x sol.f)⟩

/-- The closed subset of `tripleOfHom sol x` is the inverse image of `T`. -/
theorem tripleOfHom_Z (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (tripleOfHom sol x).Z = sol.T.preimage (Points.continuous_map x) :=
  sorry

/-- The open morphism of `tripleOfHom sol x` is the restriction of `x` followed
by the identification `X \ T ≅ U'`. -/
theorem tripleOfHom_u' (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (tripleOfHom sol x).u' =
      openComplementAlong.map x sol.T ≫ openComplementIsoInv sol :=
  sorry

/-- The completion morphism of `tripleOfHom sol x` is `a ∘ x_/Z`. -/
theorem tripleOfHom_hatx (sol : SolutionFor σ X) {V : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V.left] (x : ofOver V ⟶ X) :
    (tripleOfHom sol x).hatx = completionAlong.map x sol.T ≫ sol.a :=
  sorry

/-- The natural transformation `Mor_S(-, X) ⟶ F` with components `tripleOfHom`. -/
def ofHomNatTrans (sol : SolutionFor σ X) :
    homOnLocallyNoetherian X ⟶ σ.functor where
  app V := ofHom fun x ↦ tripleOfHom sol x
  naturality := sorry

/-- Components of `ofHomNatTrans` are `tripleOfHom`. -/
theorem ofHomNatTrans_app (sol : SolutionFor σ X)
    (V : (locallyNoetherian S).FullSubcategory) (x : ofOver V.obj ⟶ X) :
    (ofHomNatTrans sol).app (op V) x = tripleOfHom sol x :=
  sorry

/-- `tripleOfHom` is natural in morphisms of locally Noetherian schemes over
`S`. -/
theorem tripleOfHom_map (sol : SolutionFor σ X) {V1 V2 : Over S}
    [AlgebraicGeometry.IsLocallyNoetherian V1.left] [AlgebraicGeometry.IsLocallyNoetherian V2.left]
    (φ : V2 ⟶ V1) (x : ofOver V1 ⟶ X) :
    Triple.map φ (tripleOfHom sol x) = tripleOfHom sol (ofOverMap φ ≫ x) :=
  sorry

end SolutionFor

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
