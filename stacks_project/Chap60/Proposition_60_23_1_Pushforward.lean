/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Pushforward.Abelian
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline

universe u

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallinePushforward :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P],
    Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u} ⥤
      Sheaf X.smallZariskiTopology AddCommGrpCat.{u})

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallinePushforward_eq :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P],
    smallCrystallinePushforward I γ h_compatible s x₀ h_p =
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).sheafPushforwardCocontinuous
        AddCommGrpCat.{u} (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
        X.smallZariskiTopology)

#check (AlgebraicGeometry.Scheme.Crystalline.smallCrystallinePushforward_additive :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P],
    (smallCrystallinePushforward I γ h_compatible s x₀ h_p).Additive)

#check (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})],
    DerivedCategory
        (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}) ⥤
      DerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_eq :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})],
    derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p =
      Functor.RightDerived.KInjective.functor
        (smallCrystallinePushforward I γ h_compatible s x₀ h_p))

#check (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_obj :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}),
    DerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Crystalline.derivedSmallCrystallinePushforward_obj_eq :
    ∀ {p : ℕ} [Fact (Nat.Prime p)]
      {S : Scheme.{u}} (I : S.IdealSheafData)
      (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
      (h_compatible :
        ∀ (V : S.affineOpens) (f : Γ(S, V)),
          (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
            (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
      (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
      {X : Scheme.{u}} (x₀ : X ⟶ I.subscheme)
      (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    [HasSheafify
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}]
    [∀ P : (smallCrystallineSite S I γ h_compatible X x₀)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (forgetfulFunctor p S I γ h_compatible s X x₀ h_p).op.HasPointwiseRightKanExtension P]
    [HasSheafify X.smallZariskiTopology AddCommGrpCat.{u}]
    [HasDerivedCategory
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    [HasDerivedCategory (Sheaf X.smallZariskiTopology AddCommGrpCat.{u})]
    [IsGrothendieckAbelian
      (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u})]
    (G : Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p) AddCommGrpCat.{u}),
    derivedSmallCrystallinePushforward_obj I γ h_compatible s x₀ h_p G =
      (derivedSmallCrystallinePushforward I γ h_compatible s x₀ h_p).obj
        ((DerivedCategory.singleFunctor _ 0).obj G))
