/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.FiniteType
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible cohomology under derived compact-support pushforward

A separated morphism of finite presentation of quasi-compact quasi-separated
schemes preserves complexes with constructible cohomology sheaves under the
derived compact-support functor `Rf_!`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y)
variable [IsSeparated X.hom] [Scheme.Hom.FinitePresentation X.hom]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable (P : Compactification.Of Y X)
variable (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
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
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ X.left) (G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable (K : EtaleDerived X.left Λ)

namespace etaleDerivedLowerShriek

/-- Theorem 63.14.5 (1): if `f = X.hom : X.left ⟶ Y` is a separated morphism of
finite presentation of quasi-compact quasi-separated schemes, `Λ` is a
Noetherian ring, and `K` is an object of `D⁺_tors,c(X_étale, Λ)`, then
`Rf_! K` has constructible cohomology sheaves, i.e. lies in
`D⁺_tors,c(Y_étale, Λ)`. -/
@[stacks 0GL0]
theorem cohomologyIn_constructible_of_plusTorsionConstructible
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj K) :=
  sorry

/-- Theorem 63.14.5 (2): if `f = X.hom : X.left ⟶ Y` is a separated morphism of
finite presentation of quasi-compact quasi-separated schemes, `Λ` is a
Noetherian torsion ring, and `K` is an object of `D_c(X_étale, Λ)`, then
`Rf_! K` has constructible cohomology sheaves, i.e. lies in
`D_c(Y_étale, Λ)`. -/
@[stacks 0GL0]
theorem cohomologyIn_constructible_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ)
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek X P).obj K) :=
  sorry

/-- Each homology sheaf of `Rf_! K` is a constructible étale sheaf of
`Λ`-modules on `Y` when `K` lies in `D⁺_tors,c(X_étale, Λ)`. -/
theorem homology_isConstructibleEtaleModule_of_plusTorsionConstructible
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n]
    (m : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) m).obj
        ((etaleDerivedLowerShriek X P).obj K)) :=
  sorry

/-- Each homology sheaf of `Rf_! K` is a constructible étale sheaf of
`Λ`-modules on `Y` when `Λ` is torsion and `K` lies in `D_c(X_étale, Λ)`. -/
theorem homology_isConstructibleEtaleModule_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ)
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (m : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) m).obj
        ((etaleDerivedLowerShriek X P).obj K)) :=
  sorry

/-- `Rf_!` sends objects of `D⁺_tors,c(X_étale, Λ)` to complexes with torsion
cohomology sheaves on `Y`. -/
theorem etaleDerivedIsTorsion_obj_of_plusTorsionConstructible
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    etaleDerivedIsTorsion ((etaleDerivedLowerShriek X P).obj K) :=
  sorry

/-- `Rf_!` sends objects of `D⁺_tors,c(X_étale, Λ)` to bounded-below complexes
on `Y`. -/
theorem exists_isGE_obj_of_plusTorsionConstructible
    (h_cons :
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule
          (fun {Z} g ↦
            ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
              X.left.smallEtaleTopology Z.smallEtaleTopology).obj)
          (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)) K)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    ∃ m : ℤ, DerivedCategory.IsGE ((etaleDerivedLowerShriek X P).obj K) m :=
  sorry

end etaleDerivedLowerShriek

end AlgebraicGeometry.Scheme.Etale

end
