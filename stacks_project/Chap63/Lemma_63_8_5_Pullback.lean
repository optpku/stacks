/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Module.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Exactness
public import stacks_project.Chap59.Definition_59_77_1

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open CategoryTheory.Sheaf
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Inverse image of small-étale sheaves of `Λ`-modules along a morphism of
schemes. -/
abbrev etaleModuleSheafPullback {A B : Scheme.{u}} (h : A ⟶ B) (Λ : Type u)
    [Ring Λ]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback h).op.HasLeftKanExtension P] :
    Sheaf B.smallEtaleTopology (ModuleCat.{u} Λ) ⥤
      Sheaf A.smallEtaleTopology (ModuleCat.{u} Λ) :=
  Sheaf.smallEtaleInverseImage h (ModuleCat.{u} Λ)

/-- Pullback of module sheaves along a composite is the composite pullback. -/
def etaleModuleSheafPullback_comp {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
    (Λ : Type u) [Ring Λ]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback p).op.HasLeftKanExtension P]
    [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback q).op.HasLeftKanExtension P]
    [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension P] :
    etaleModuleSheafPullback p Λ ⋙ etaleModuleSheafPullback q Λ ≅
      etaleModuleSheafPullback (q ≫ p) Λ :=
  Hom.etaleModuleSheafPullback_comp Λ p q


section CompatibilityChecks

variable {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
variable (Λ : Type u) [Ring Λ]
variable [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback p).op.HasLeftKanExtension P]
variable [∀ P : B.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback q).op.HasLeftKanExtension P]
variable [∀ P : A.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (q ≫ p)).op.HasLeftKanExtension P]

/- Canonical composition remains available through the historical argument order. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleModuleSheafPullback_comp p q Λ :
  etaleModuleSheafPullback p Λ ⋙ etaleModuleSheafPullback q Λ ≅
    etaleModuleSheafPullback (q ≫ p) Λ)

/- Canonical pullback retains its defining sheaf-pullback expression. -/
#check (AlgebraicGeometry.Scheme.Hom.etaleModuleSheafPullback_eq Λ p :
  etaleModuleSheafPullback p Λ =
    (smallEtalePullback p).sheafPullback (ModuleCat.{u} Λ)
      A.smallEtaleTopology B.smallEtaleTopology)

end CompatibilityChecks

end AlgebraicGeometry.Scheme.Etale

end
