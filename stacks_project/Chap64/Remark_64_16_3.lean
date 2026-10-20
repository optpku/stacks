/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupportTrace
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.WeilTrace
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.CompactSupportTrace
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open CategoryTheory.DerivedCategory Opposite ComplexShape
open scoped AlgebraicGeometry MonoidalCategory Ring CategoryTheory.MonObj

universe u

/- Remark 64.16.3: even though the argument of
`lefschetzTraceFormula_compactSupport` consists of reductions and mostly
algebra, that compact-support trace formula (Theorem 64.16.1) is much
stronger than Weil's geometric trace formula `weilTraceFormula`
(Theorem 64.14.4) because its coefficient input is `K` in
`EtaleConstructibleTorFinite`, not merely constant coefficients. -/
@[stacks 03UJ] #check
  (AlgebraicGeometry.SchemeOverField.lefschetzTraceFormula_compactSupport :
    ∀ {k : Type u} [Field k] [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    {Λ : Type u} [Ring Λ] [Finite Λ] [IsNoetherianRing Λ]
    [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
    [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ {Y : Scheme.{u}} (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ {Y : Scheme.{u}},
      HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
      (smallEtalePullback f).op.HasLeftKanExtension F]
    [∀ {Y : Scheme.{u}},
      ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (op (Etale.globalEtale Y))).Additive]
    [∀ {Y : Scheme.{u}},
      HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (Etale.globalEtale Y))))
        (HomologicalComplex.quasiIso
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
    [∀ Z : Scheme.{u},
      HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      PreservesFiniteLimits
        ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology)]
    [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      PreservesFiniteColimits
        ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology X.smallEtaleTopology)]
    [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology)).Additive]
    [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
      PreservesFiniteLimits
        (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
            A.smallEtaleTopology B.smallEtaleTopology) ⋙
          ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
            B.smallEtaleTopology C.smallEtaleTopology))]
    [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
      PreservesFiniteColimits
        (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
            A.smallEtaleTopology B.smallEtaleTopology) ⋙
          ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
            B.smallEtaleTopology C.smallEtaleTopology))]
    (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Projective (Over.hom P.obj.right)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (hΛ : Nat.Coprime (Nat.card Λ) (Fintype.card k))
    (K : AlgebraicGeometry.Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite
      (X := X.left) (Λ := Λ)),
    traceGeometricFrobeniusCompactSupport X P K.obj
        (isPerfect_geometricRGammaCompactSupport X P hdim hΛ K) =
      traceGeometricFrobeniusStalks K.obj
        (fun x ↦ isPerfect_geometricDerivedStalk_of_finiteRing K x))

#check (AlgebraicGeometry.Curve.weilTraceFormula :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
    (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C),
    fixedPointNumber φ hφ =
      1 - endomorphismTrace (pullbackComponentHom C φ) +
        (curveEndomorphismDegree φ : ℤ))
