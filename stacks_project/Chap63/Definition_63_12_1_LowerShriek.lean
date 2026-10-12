/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Whiskering
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Definition_59_77_1

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Continuous small-étale pushforward of sheaves of `Λ`-modules. -/
def etaleModulePushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u)
    [CommRing Λ] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ) :=
  (smallEtalePullback f).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology

/-- Small-étale module pushforward is continuous sheaf pushforward along
`smallEtalePullback`. -/
theorem etaleModulePushforward_def {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type u)
    [CommRing Λ] :
    etaleModulePushforward f Λ =
      (smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology := sorry

section Torsion

variable {X : Scheme.{u}} {Λ : Type u} [CommRing Λ]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- An object of `D(X_étale, Λ)` has torsion cohomology sheaves when each
homology sheaf is locally torsion after forgetting from `Λ`-modules to abelian
groups. This is the source domain condition for `D⁺_tors(X_étale, Λ)`. -/
def etaleDerivedIsTorsion (K : EtaleDerived X Λ) : Prop :=
  ∀ n : ℤ,
    IsLocallyTorsion
      ((sheafCompose X.smallEtaleTopology
          (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
        ((DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj K))

/-- Torsion cohomology sheaves are detected degreewise after forgetting to
abelian étale sheaves. -/
theorem etaleDerivedIsTorsion_iff (K : EtaleDerived X Λ) :
    etaleDerivedIsTorsion K ↔
      ∀ n : ℤ,
        IsLocallyTorsion
          ((sheafCompose X.smallEtaleTopology
              (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj
            ((DerivedCategory.homologyFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj K)) :=
  sorry

end Torsion

section DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Λ : Type u} [CommRing Λ]
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
    EtaleDerived X Λ ⥤ EtaleDerived Y Λ :=
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
          (ModuleCat.{u} Λ) Y.smallEtaleTopology X.smallEtaleTopology) :=
  sorry

end DerivedPushforward

section LowerShriek

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

/-- The derived lower shriek `Rf_!` of a separated finite-type morphism with
quasi-compact quasi-separated target, realized as `R f̄_* ∘ j_!` from an
explicit compactification `j : X.left ⟶ X̄` over `Y`. -/
def etaleDerivedLowerShriek :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ :=
  (etaleExtensionByZero (Compactification.Of.ι P)
      (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
    etaleDerivedPushforward P.obj.right.hom

/-- Evaluating `Rf_!` applies extension by zero along the interior immersion
and then derived pushforward along the structure map of the compactification. -/
theorem etaleDerivedLowerShriek_obj (K : EtaleDerived X.left Λ) :
    (etaleDerivedLowerShriek X P).obj K =
      (etaleDerivedPushforward P.obj.right.hom).obj
        ((etaleExtensionByZero (Compactification.Of.ι P)
            (ModuleCat.{u} Λ)).mapDerivedCategory.obj K) := sorry

end LowerShriek

end AlgebraicGeometry.Scheme.Etale

end
