/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Etale.Gluing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.IsBlowup.Etale
open CategoryTheory.Sheaf

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

/- Lemma 59.105.3 (1): given a blow-up square of a finite-type quasi-coherent closed
subscheme, torsion objects `K'` in `D⁺(X'_étale)` and `L` in `D⁺(Z_étale)`, and an
isomorphism `γ : K'|_E ≅ L|_E`, there exist `K` in `D⁺(X_étale)` and isomorphisms
`f : K|_{X'} ≅ K'`, `g : K|_Z ≅ L` such that `γ = g|_E ∘ f⁻¹|_E`. -/
@[stacks 0EW6] #check (AlgebraicGeometry.IsBlowup.Etale.exists_of_isoOnExceptional :
    ∀ {I : X.IdealSheafData} {b : X' ⟶ X} [IsBlowup b I]
    (hI : I.IsFiniteType)
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))
    (hK' : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})) K')
    (L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u}))
    (hL : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})) L)
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L),
    ∃ (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
      (f : (etaleDerivedInverseImage b).obj K ≅ K')
      (g : (etaleDerivedInverseImage I.subschemeι).obj K ≅ L),
      IsCompatibleOnExceptional I b γ f g)

/- Lemma 59.105.3 (2): given in addition a torsion object `M` in `D⁺(X_étale)` and
compatible morphisms `α : K' ⟶ M|_{X'}`, `β : L ⟶ M|_Z`, there exists `φ : K ⟶ M` in
`D(X_étale)` with `φ|_{X'} = f.hom ≫ α` and `φ|_Z = g.hom ≫ β`. The published last
arrow `M ⟶ K` with restrictions `a ∘ f` and `b ∘ g` is type-inconsistent (`a ∘ f`
would have type `K|_{X'} ⟶ M|_{X'}`); the proof constructs `K ⟶ M`. -/
@[stacks 0EW6] #check (AlgebraicGeometry.IsBlowup.Etale.exists_hom :
    ∀ {I : X.IdealSheafData} {b : X' ⟶ X} [IsBlowup b I]
    (hI : I.IsFiniteType)
    (K' : DerivedCategory.Plus (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u}))
    (hK' : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u})) K')
    (L : DerivedCategory.Plus (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u}))
    (hL : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion :
        ObjectProperty (Sheaf I.subscheme.smallEtaleTopology AddCommGrpCat.{u})) L)
    (γ : (etaleDerivedInverseImage (I.comap b).subschemeι).obj K' ≅
      (etaleDerivedInverseImage (exceptionalProjection I b)).obj L)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) K)
    (f : (etaleDerivedInverseImage b).obj K ≅ K')
    (g : (etaleDerivedInverseImage I.subschemeι).obj K ≅ L)
    (hγ : IsCompatibleOnExceptional I b γ f g)
    (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hM : DerivedCategory.Plus.cohomologyIn
      (IsLocallyTorsion : ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) M)
    (α : K' ⟶ (etaleDerivedInverseImage b).obj M)
    (β : L ⟶ (etaleDerivedInverseImage I.subschemeι).obj M)
    (hαβ : IsCompatibleRestrictions I b γ α β),
    ∃ φ : K ⟶ M, (etaleDerivedInverseImage b).map φ = f.hom ≫ α ∧
      (etaleDerivedInverseImage I.subschemeι).map φ = g.hom ≫ β)

end AlgebraicGeometry.IsBlowup.Etale

end

end
