/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Etale.Comparison

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.IsBlowup.Etale
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow

noncomputable section

universe w u

namespace AlgebraicGeometry.IsBlowup.Etale

variable {X X' : Scheme.{u}}
variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (p : A ⟶ B),
    (abelianPushforwardAlong p).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]
variable [∀ {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C),
    (abelianPushforwardAlong f ⋙ abelianPushforwardAlong g).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf A.smallEtaleTopology AddCommGrpCat.{u}))]

/-- For a scheme `X` and a closed subscheme cut out by a quasi-coherent
ideal of finite type, the corresponding blow-up square yields, for every
`K ∈ D⁺(X_étale)` with torsion cohomology sheaves, a distinguished triangle
`K ⟶ Ri_*(K|_Z) ⊕ Rb_*(K|_{X'}) ⟶ Rc_*(K|_E) ⟶ K⟦1⟧` in `D(X_étale)`, where
`c = i ∘ π = b ∘ j`. -/
theorem distinguishedTriangle {I : X.IdealSheafData} {b : X' ⟶ X} [IsBlowup b I]
    (hI : I.IsFiniteType)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) K) :
    ∃ δ : (square I b K).shortComplex'.X₃ ⟶ (square I b K).shortComplex'.X₁⟦(1 : ℤ)⟧,
      Triangle.mk (square I b K).shortComplex'.f (square I b K).shortComplex'.g δ ∈
        distTriang (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) := sorry

end AlgebraicGeometry.IsBlowup.Etale

end

end
