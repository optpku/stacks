/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.Restriction
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry

noncomputable section

universe u w u₁ v₁

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable {U X : Scheme.{u}}

/-- The restriction functor induced on sheaves by a weakly étale morphism. -/
abbrev restrictionSheaf (j : U ⟶ X) [WeaklyEtale j] (A : Type u₁) [Category.{v₁} A] :
    Sheaf (topology X) A ⥤ Sheaf (topology U) A :=
  (restriction j).sheafPushforwardContinuous A (topology U) (topology X)

/-- Under the canonical Kan-extension and sheafification hypotheses, pro-étale
sheaf restriction is a right adjoint. -/
instance restrictionSheaf_isRightAdjoint (j : U ⟶ X) [WeaklyEtale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) A] :
    (restrictionSheaf j A).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (restriction j) A (topology U) (topology X)).isRightAdjoint

/-- The canonical sheaf-valued extension-by-zero functor along a weakly étale
morphism, given by the sheaf pullback of pro-étale restriction. -/
noncomputable abbrev extensionByZero (j : U ⟶ X) [WeaklyEtale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) A] :
    Sheaf (topology U) A ⥤ Sheaf (topology X) A :=
  Functor.sheafPullback (restriction j) A (topology U) (topology X)

/-- The canonical adjunction for pro-étale extension by zero and restriction. -/
def extensionByZero_adjunction (j : U ⟶ X) [WeaklyEtale j]
    (A : Type u₁) [Category.{v₁} A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) A] :
    extensionByZero j A ⊣ restrictionSheaf j A :=
  Functor.sheafAdjunctionContinuous (restriction j) A (topology U) (topology X)

/-- Extension by zero for sheaves of sets. -/
noncomputable abbrev sheafExtensionByZero (j : U ⟶ X) [WeaklyEtale j]
    [∀ F : U.ProEtᵒᵖ ⥤ Type w, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) (Type w)] :
    Sheaf (topology U) (Type w) ⥤ Sheaf (topology X) (Type w) :=
  extensionByZero j (Type w)

/-- The extension-by-zero/restriction adjunction for sheaves of sets. -/
def sheafExtensionByZero_adjunction (j : U ⟶ X) [WeaklyEtale j]
    [∀ F : U.ProEtᵒᵖ ⥤ Type w, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) (Type w)] :
    sheafExtensionByZero j ⊣ restrictionSheaf j (Type w) :=
  extensionByZero_adjunction j (Type w)

/-- Extension by zero for sheaves of abelian groups. -/
noncomputable abbrev abelianExtensionByZero (j : U ⟶ X) [WeaklyEtale j]
    [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) AddCommGrpCat.{w}] :
    Sheaf (topology U) AddCommGrpCat.{w} ⥤ Sheaf (topology X) AddCommGrpCat.{w} :=
  extensionByZero j AddCommGrpCat.{w}

/-- The extension-by-zero/restriction adjunction for sheaves of abelian
groups. -/
def abelianExtensionByZero_adjunction (j : U ⟶ X) [WeaklyEtale j]
    [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) AddCommGrpCat.{w}] :
    abelianExtensionByZero j ⊣ restrictionSheaf j AddCommGrpCat.{w} :=
  extensionByZero_adjunction j AddCommGrpCat.{w}

/-- Let `j : U ⟶ X` be weakly étale and `i : Z ⟶ X` a closed immersion
with empty pullback. If `V` is an affine pro-étale object over `X` whose
points all specialize to points over `Z`, then the sections on `V` of
extension by zero along `j` of any abelian sheaf on `U` form a zero object. -/
theorem abelianExtensionByZero_sections_isZero
    {U X Z : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    [IsEmpty (pullback j i : Scheme.{u})]
    (V : X.ProEt) [IsAffine V.left]
    (hV : ∀ x : V.left,
      ∃ z : (pullback i V.hom : Scheme.{u}),
        x ⤳ (pullback.snd i V.hom) z)
    [∀ F : U.ProEtᵒᵖ ⥤ AddCommGrpCat.{w},
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) AddCommGrpCat.{w}]
    (F : Sheaf (topology U) AddCommGrpCat.{w}) :
    IsZero (((abelianExtensionByZero j).obj F).obj.obj (op V)) :=
  sorry

variable {Λ : Type w} [Ring Λ]

/-- Extension by zero for sheaves of `Λ`-modules. -/
noncomputable abbrev moduleExtensionByZero (j : U ⟶ X) [WeaklyEtale j]
    [∀ F : U.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ,
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)] :
    Sheaf (topology U) (ModuleCat.{w} Λ) ⥤ Sheaf (topology X) (ModuleCat.{w} Λ) :=
  extensionByZero j (ModuleCat.{w} Λ)

/-- The extension-by-zero/restriction adjunction for sheaves of `Λ`-modules. -/
def moduleExtensionByZero_adjunction (j : U ⟶ X) [WeaklyEtale j]
    [∀ F : U.ProEtᵒᵖ ⥤ ModuleCat.{w} Λ,
      (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology X) (ModuleCat.{w} Λ)] :
    moduleExtensionByZero j ⊣ restrictionSheaf j (ModuleCat.{w} Λ) :=
  extensionByZero_adjunction j (ModuleCat.{w} Λ)

end ProEt

end AlgebraicGeometry.Scheme
