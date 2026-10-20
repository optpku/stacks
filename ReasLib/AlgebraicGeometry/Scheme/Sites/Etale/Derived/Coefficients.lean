module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Acyclicity
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.GlobalSections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Continuous small-étale pushforward of sheaves of `Λ`-modules. -/
def etaleModulePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u)
    [Ring Λ] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- Small-étale module pushforward is continuous sheaf pushforward along
`smallEtalePullback`. -/
theorem etaleModulePushforward_def {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u)
    [Ring Λ] :
    etaleModulePushforward f Λ =
      (smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Continuous small-étale module pushforward commutes with forgetting from
`Λ`-modules to abelian groups. -/
def etaleModulePushforward_compSheafComposeIso {S T : Scheme.{u}} (h : S ⟶ T)
    (Λ : Type u) [Ring Λ]
    [S.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [T.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})] :
    etaleModulePushforward h Λ ⋙
        sheafCompose T.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ≅
      sheafCompose S.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) ⋙
        etaleAbelianPushforward h :=
  Functor.fullyFaithfulCancelRight
    (sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u}) (Iso.refl _)

/-- Unfolding `etaleModulePushforward` recovers additivity of the underlying
continuous small-étale module pushforward. -/
instance etaleModulePushforward_sheafPushforwardContinuous_additive
    {S T : Scheme.{u}} (h : S ⟶ T) {R : Type u} [Ring R]
    [hF : (etaleModulePushforward h R).Additive] :
    ((smallEtalePullback h).sheafPushforwardContinuous
      (ModuleCat.{u} R) T.smallEtaleTopology S.smallEtaleTopology).Additive :=
  hF

section Torsion

variable {X : Scheme.{u}} {Λ : Type u} [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- An object of `D(X_étale, Λ)` has torsion cohomology sheaves when each
homology sheaf is locally torsion after forgetting from `Λ`-modules to abelian
groups. -/
def etaleDerivedIsTorsion (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) : Prop :=
  ∀ n : ℤ,
    IsLocallyTorsion
      ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj K))

/-- Torsion cohomology sheaves are detected degreewise after forgetting to
abelian étale sheaves. -/
theorem etaleDerivedIsTorsion_iff (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    etaleDerivedIsTorsion K ↔
      ∀ n : ℤ,
        IsLocallyTorsion
          ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
            ((DerivedCategory.homologyFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj K)) := sorry

end Torsion

section DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ : Type u} [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived small-étale pushforward `Rf_*` of sheaves of `Λ`-modules. -/
def etaleDerivedPushforward
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  RightDerived.Cochain.functor
    ((smallEtalePullback f).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology)

/-- Derived étale pushforward is the cochain-level total right derived functor of
continuous small-étale module pushforward. -/
theorem etaleDerivedPushforward_def
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))] :
    etaleDerivedPushforward f =
      RightDerived.Cochain.functor
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology) := sorry

end DerivedPushforward

section DerivedGamma

variable (X : Scheme.{u}) (Λ : Type u) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale X))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale X))))
  (HomologicalComplex.quasiIso
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Derived global sections `RΓ(X, -)` on `D(X_étale, Λ)`, obtained as the
total right derived functor of small-étale module sections at `globalEtale X`. -/
def etaleDerivedGamma :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (ModuleCat.{u} Λ) :=
  RightDerived.Cochain.functor
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale X)))

/-- `RΓ(X, -)` is the cochain-level total right derived functor of sections at
the terminal object of `X_étale`. -/
theorem etaleDerivedGamma_def :
    etaleDerivedGamma X Λ =
      RightDerived.Cochain.functor
        ((sheafSections X.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale X))) := sorry

end DerivedGamma

namespace Derived

section Admissible

variable (X : Scheme.{u}) (Λ : Type u) [Ring Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- The objects with bounded-below torsion cohomology, together with all objects
when the coefficient ring is additively torsion. -/
def compactSupportAdmissible :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  fun K ↦ (etaleDerivedIsTorsion K ∧ ∃ n : ℤ, K.IsGE n) ∨ AddMonoid.IsTorsion Λ

/-- An object is admissible exactly when it has bounded-below torsion cohomology
or the coefficient ring is additively torsion. -/
theorem compactSupportAdmissible_iff
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) :
    compactSupportAdmissible X Λ K ↔
      (etaleDerivedIsTorsion K ∧ ∃ n : ℤ, K.IsGE n) ∨ AddMonoid.IsTorsion Λ := sorry

end Admissible

end Derived

end AlgebraicGeometry.Scheme.Etale

end
