/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Restriction
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u w u₁ v₁

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}}

/-- The restriction functor induced on sheaves by an étale morphism. -/
abbrev etaleRestrictionSheaf (j : U ⟶ X) [Etale j] (A : Type u₁) [Category.{v₁} A] :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf U.smallEtaleTopology A :=
  (etaleRestriction j).sheafPushforwardContinuous A
    U.smallEtaleTopology X.smallEtaleTopology

/-- The sheaf restriction functor is the continuous sheaf pushforward. -/
theorem etaleRestrictionSheaf_def (j : U ⟶ X) [Etale j]
    (A : Type u₁) [Category.{v₁} A] :
    etaleRestrictionSheaf j A =
      (etaleRestriction j).sheafPushforwardContinuous A
        U.smallEtaleTopology X.smallEtaleTopology := sorry

/-- Under the canonical Kan-extension and sheafification hypotheses, étale
sheaf restriction is a right adjoint. -/
instance etaleRestrictionSheaf_isRightAdjoint (j : U ⟶ X) [Etale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.Etaleᵒᵖ ⥤ A, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology A] :
    (etaleRestrictionSheaf j A).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (etaleRestriction j) A U.smallEtaleTopology X.smallEtaleTopology).isRightAdjoint

/-- The canonical sheaf-valued extension-by-zero functor along an étale
morphism, given by the sheaf pullback of étale restriction. -/
noncomputable abbrev etaleExtensionByZero (j : U ⟶ X) [Etale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.Etaleᵒᵖ ⥤ A, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology A] :
    Sheaf U.smallEtaleTopology A ⥤ Sheaf X.smallEtaleTopology A :=
  Functor.sheafPullback (etaleRestriction j) A
    U.smallEtaleTopology X.smallEtaleTopology

/-- Étale extension by zero is the canonical sheaf pullback. -/
theorem etaleExtensionByZero_def (j : U ⟶ X) [Etale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.Etaleᵒᵖ ⥤ A, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology A] :
    etaleExtensionByZero j A =
      Functor.sheafPullback (etaleRestriction j) A
        U.smallEtaleTopology X.smallEtaleTopology := sorry

/-- The canonical adjunction for étale extension by zero and restriction. -/
def etaleExtensionByZero_adjunction (j : U ⟶ X) [Etale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.Etaleᵒᵖ ⥤ A, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology A] :
    etaleExtensionByZero j A ⊣ etaleRestrictionSheaf j A :=
  Functor.sheafAdjunctionContinuous (etaleRestriction j) A
    U.smallEtaleTopology X.smallEtaleTopology

/-- Extension by zero for sheaves of sets. -/
noncomputable abbrev sheafExtensionByZero (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ Type w, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (Type w)] :
    Sheaf U.smallEtaleTopology (Type w) ⥤
      Sheaf X.smallEtaleTopology (Type w) :=
  etaleExtensionByZero j (Type w)

/-- Sheaf-valued extension by zero is the generic étale extension functor. -/
theorem sheafExtensionByZero_def (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ Type w, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (Type w)] :
    sheafExtensionByZero j = etaleExtensionByZero j (Type w) := sorry

/-- The extension-by-zero/restriction adjunction for sheaves of sets. -/
def sheafExtensionByZero_adjunction (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ Type w, (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (Type w)] :
    sheafExtensionByZero j ⊣ etaleRestrictionSheaf j (Type w) :=
  etaleExtensionByZero_adjunction j (Type w)

/-- Extension by zero for sheaves of abelian groups. -/
noncomputable abbrev abelianExtensionByZero (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}] :
    Sheaf U.smallEtaleTopology AddCommGrpCat.{w} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{w} :=
  etaleExtensionByZero j AddCommGrpCat.{w}

/-- Abelian extension by zero is the generic étale extension functor. -/
theorem abelianExtensionByZero_def (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}] :
    abelianExtensionByZero j = etaleExtensionByZero j AddCommGrpCat.{w} := sorry

/-- The extension-by-zero/restriction adjunction for sheaves of abelian
groups. -/
def abelianExtensionByZero_adjunction (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}] :
    abelianExtensionByZero j ⊣ etaleRestrictionSheaf j AddCommGrpCat.{w} :=
  etaleExtensionByZero_adjunction j AddCommGrpCat.{w}

variable {Λ : Type w} [Ring Λ]

/-- Extension by zero for sheaves of `Λ`-modules. -/
noncomputable abbrev moduleExtensionByZero (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)] :
    Sheaf U.smallEtaleTopology (ModuleCat.{w} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ) :=
  etaleExtensionByZero j (ModuleCat.{w} Λ)

/-- Module extension by zero is the generic étale extension functor. -/
theorem moduleExtensionByZero_def (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)] :
    moduleExtensionByZero j = etaleExtensionByZero j (ModuleCat.{w} Λ) := sorry

/-- The extension-by-zero/restriction adjunction for étale sheaves of
`Λ`-modules. -/
def moduleExtensionByZero_adjunction (j : U ⟶ X) [Etale j]
    [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ,
      (etaleRestriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{w} Λ)] :
    moduleExtensionByZero j ⊣ etaleRestrictionSheaf j (ModuleCat.{w} Λ) :=
  etaleExtensionByZero_adjunction j (ModuleCat.{w} Λ)

end AlgebraicGeometry.Scheme
