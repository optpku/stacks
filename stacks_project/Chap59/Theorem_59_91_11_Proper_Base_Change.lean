module

public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]

/-- Theorem 59.91.11 (Proper Base Change): if `f : X ⟶ Y` is a proper morphism of
schemes, then cohomology commutes with base change for `f`. Equivalently, for every
cartesian square with legs `g : Y' ⟶ Y`, `f' : X' ⟶ Y'`, `g' : X' ⟶ X` and every
locally torsion abelian étale sheaf `F` on `X`, the canonical base-change map
`g⁻¹ Rf_* F ⟶ Rf'_* (g')⁻¹ F` is an isomorphism. -/
@[stacks 095T]
theorem cohomologyCommutesWithBaseChange_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange f := sorry

/-- Unpacking of `cohomologyCommutesWithBaseChange_of_isProper`: on a cartesian
square, the named degree-`q` comparison `higherDirectImage_baseChangeHom` is an
isomorphism for every locally torsion abelian étale sheaf. -/
theorem higherDirectImage_baseChangeHom_isIso_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (h_cart : IsPullback g' f' f g)
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} (hF : IsLocallyTorsion F)
    (q : ℕ) :
    IsIso (higherDirectImage_baseChangeHom f g f' g' h_cart F q) := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
