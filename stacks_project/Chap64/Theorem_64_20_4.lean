module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFiniteTrace
public import stacks_project.Chap59.Definition_59_77_1

/-!
# Lefschetz trace formula for constructible complexes of finite Tor-dimension
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.CompactSupportTrace
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory Opposite ComplexShape
open scoped AlgebraicGeometry MonoidalCategory Ring

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {Λ : Type u} [Ring Λ] [Finite Λ] [IsNoetherianRing Λ]
variable [HasColimitsOfSize.{u, u} (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}}, HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}} (U : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ {Y : Scheme.{u}},
    HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (Etale.globalEtale Y))).Additive]
variable [∀ {Y : Scheme.{u}},
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (Etale.globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
    (smallEtalePullback f).op.HasLeftKanExtension F]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
      Y.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits
      ((smallEtalePullback f).sheafPullback (ModuleCat.{u} Λ)
        Y.smallEtaleTopology X.smallEtaleTopology)]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
        A.smallEtaleTopology B.smallEtaleTopology) ⋙
      ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
        B.smallEtaleTopology C.smallEtaleTopology)).Additive]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteLimits
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteColimits
      (((smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
          A.smallEtaleTopology B.smallEtaleTopology) ⋙
        ((smallEtalePullback q).sheafPullback (ModuleCat.{u} Λ)
          B.smallEtaleTopology C.smallEtaleTopology))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)).Additive]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))]
variable [∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
      Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ)).Additive]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteLimits
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ))]
variable [∀ {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B),
    PreservesFiniteColimits
      (Sheaf.smallEtaleInverseImage p (ModuleCat.{u} Λ) ⋙
        Sheaf.smallEtaleInverseImage q (ModuleCat.{u} Λ))]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {Y : Scheme.{u}},
    MonoidalCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}},
    MonoidalPreadditive (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ {Y : Scheme.{u}}
    (K L : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (ComplexShape.up ℤ)]
variable [∀ {Y : Scheme.{u}},
    DerivedTensor.Right.Has
      (C := Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/- Theorem 64.20.4 (1). -/
@[stacks 03V3] #check
  (AlgebraicGeometry.SchemeOverField.isPerfect_geometricRGammaCompactSupport_of_constructibleTorFinite :
    ∀ (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (K : AlgebraicGeometry.Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite
      (X := X.left) (Λ := Λ)),
    DerivedCategory.IsPerfect (geometricRGammaCompactSupport X P K.obj))

/- Theorem 64.20.4 (2). -/
@[stacks 03V3] #check
  (AlgebraicGeometry.SchemeOverField.lefschetzTraceFormula_of_constructibleTorFinite :
    ∀ (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
    [(etaleExtensionByZero (Compactification.Of.ι P)
        (ModuleCat.{u} Λ)).Additive]
    [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
    (hΛ : Nat.Coprime (Nat.card Λ) p)
    (K : AlgebraicGeometry.Scheme.Etale.Derived.FiniteRing.ConstructibleTorFinite
      (X := X.left) (Λ := Λ)),
    traceGeometricFrobeniusCompactSupport X P K.obj
        (isPerfect_geometricRGammaCompactSupport_of_constructibleTorFinite X P hΛ K) =
      traceGeometricFrobeniusStalks K.obj
        (fun x ↦ isPerfect_geometricDerivedStalk_of_finiteRing K x))

end AlgebraicGeometry.SchemeOverField
