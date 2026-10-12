/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap63.Lemma_63_7_1_Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible cohomology under compact-support direct image

A locally quasi-finite morphism of finite presentation preserves complexes
with constructible cohomology sheaves under the exact compact-support functor
`f_!` of Lemma 63.7.1.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]
  [Scheme.Hom.FinitePresentation f]
variable (Λ : Type u) [CommRing Λ] [IsNoetherianRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ X) (G : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Lemma 63.14.1: if `f : X ⟶ Y` is locally quasi-finite and of finite
presentation, then the exact compact-support functor
`f_! = lowerShriekModuleDerived : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` of
Lemma 63.7.1 sends `D_c(X_étale, Λ)` into `D_c(Y_étale, Λ)`. -/
@[stacks 0GK3]
theorem lowerShriekModuleDerived_mem_constructibleCategory
    (K : EtaleConstructibleCategory X Λ
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            X.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((lowerShriekModuleDerived f Λ).obj K.obj) :=
  sorry

/-- Each homology sheaf of `f_! K` is a constructible étale sheaf of `Λ`-modules
on `Y`. -/
theorem lowerShriekModuleDerived_homology_isConstructibleEtaleModule
    (K : EtaleConstructibleCategory X Λ
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            X.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)))
    (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((lowerShriekModuleDerived f Λ).obj K.obj)) :=
  sorry

/-- Compact-support direct image along a locally quasi-finite morphism of finite
presentation sends constructible étale sheaves of `Λ`-modules to constructible
étale sheaves of `Λ`-modules. -/
theorem lowerShriekModule_isConstructibleEtaleModule
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))
    (hF : Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          X.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((lowerShriekModule f Λ).obj F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
