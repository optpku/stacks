/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.OpenImmersion

/-!
# Compactification of underived étale lower shriek

For an open immersion into a scheme proper over the base, compact-support
pushforward is canonically isomorphic to extension by zero followed by
pushforward along the proper structure morphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Xbar Y : Scheme.{u}} (j : X ⟶ Xbar) (fbar : Xbar ⟶ Y)
variable [IsOpenImmersion j] [IsProper fbar]
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasWeakSheafify Xbar.smallEtaleTopology AddCommGrpCat.{u}]

/-- The canonical comparison `f_! ⟶ f̄_! ∘ j_!` of underived compact-support
pushforwards along an open immersion `j : X ⟶ X̄` into a proper `Y`-scheme,
obtained by whiskering the extension-by-zero unit and then applying
`etaleLowerShriekOpenImmersion` to `j_!`. -/
def etaleLowerShriekCompactify :
    etaleLowerShriek (j ≫ fbar) ⟶
      abelianExtensionByZero j ⋙ etaleLowerShriek fbar :=
  whiskerRight (abelianExtensionByZero_adjunction j).unit
      (etaleLowerShriek (j ≫ fbar)) ≫
    whiskerLeft (abelianExtensionByZero j)
      (etaleLowerShriekOpenImmersion j fbar)

/-- The compactification comparison at an abelian étale sheaf `F`. -/
def etaleLowerShriekCompactify_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriek (j ≫ fbar)).obj F ⟶
      (etaleLowerShriek fbar).obj ((abelianExtensionByZero j).obj F) :=
  (etaleLowerShriekCompactify j fbar).app F

/-- The sheaf-level component of `etaleLowerShriekCompactify` is its
natural-transformation component. -/
theorem etaleLowerShriekCompactify_app_def
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCompactify_app j fbar F =
      (etaleLowerShriekCompactify j fbar).app F :=
  sorry

/-- The compactification comparison is the whiskered unit followed by
covariance along the open immersion. -/
theorem etaleLowerShriekCompactify_hom :
    etaleLowerShriekCompactify j fbar =
      whiskerRight (abelianExtensionByZero_adjunction j).unit
          (etaleLowerShriek (j ≫ fbar)) ≫
        whiskerLeft (abelianExtensionByZero j)
          (etaleLowerShriekOpenImmersion j fbar) :=
  sorry

/-- The compactification comparison `etaleLowerShriekCompactify` is an
isomorphism. -/
instance etaleLowerShriekCompactify_isIso :
    IsIso (etaleLowerShriekCompactify j fbar) :=
  sorry

/-- Compact-support pushforward along an equal structure morphism `f = j ≫ f̄`
is identified with `f̄_! ∘ j_!` via `etaleLowerShriekCongr`. -/
def etaleLowerShriekCompactifyIso_eq (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] (hf : j ≫ fbar = f) :
    etaleLowerShriek f ≅
      abelianExtensionByZero j ⋙ etaleLowerShriek fbar :=
  etaleLowerShriekCongr hf.symm ≪≫ asIso (etaleLowerShriekCompactify j fbar)

/-- The forward map of `etaleLowerShriekCompactifyIso_eq` is congruence
followed by the compactification comparison. -/
theorem etaleLowerShriekCompactifyIso_eq_hom (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] (hf : j ≫ fbar = f) :
    (etaleLowerShriekCompactifyIso_eq j fbar f hf).hom =
      (etaleLowerShriekCongr hf.symm).hom ≫
        etaleLowerShriekCompactify j fbar :=
  sorry


/-- Compact-support pushforward along an open immersion into a proper scheme
is canonically isomorphic to extension by zero followed by compact-support
pushforward along the proper structure morphism. -/
def etaleLowerShriekCompactifyIso :
    etaleLowerShriek (j ≫ fbar) ≅
      abelianExtensionByZero j ⋙ etaleLowerShriek fbar :=
  asIso (etaleLowerShriekCompactify j fbar)

/-- The compactification comparison isomorphism at an abelian étale sheaf `F`. -/
def etaleLowerShriekCompactifyIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriek (j ≫ fbar)).obj F ≅
      (etaleLowerShriek fbar).obj ((abelianExtensionByZero j).obj F) :=
  (etaleLowerShriekCompactifyIso j fbar).app F

/-- The objectwise identification is the component of
`etaleLowerShriekCompactifyIso`. -/
theorem etaleLowerShriekCompactifyIso_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCompactifyIso_app j fbar F =
      (etaleLowerShriekCompactifyIso j fbar).app F :=
  sorry

/-- The forward map of `etaleLowerShriekCompactifyIso` is the compactification
comparison natural transformation. -/
theorem etaleLowerShriekCompactifyIso_hom :
    (etaleLowerShriekCompactifyIso j fbar).hom =
      etaleLowerShriekCompactify j fbar :=
  sorry

/-- Compact-support pushforward along an open immersion into a proper scheme
is canonically isomorphic to extension by zero followed by ordinary
small-étale pushforward along the proper structure morphism. -/
def etaleLowerShriekCompactifyPushforwardIso :
    etaleLowerShriek (j ≫ fbar) ≅
      abelianExtensionByZero j ⋙ etaleAbelianPushforward fbar :=
  etaleLowerShriekCompactifyIso j fbar ≪≫
    isoWhiskerLeft (abelianExtensionByZero j) (etaleLowerShriekIso fbar)

/-- The pushforward form of the compactification comparison at an abelian étale sheaf `F`. -/
def etaleLowerShriekCompactifyPushforwardIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriek (j ≫ fbar)).obj F ≅
      (etaleAbelianPushforward fbar).obj ((abelianExtensionByZero j).obj F) :=
  (etaleLowerShriekCompactifyPushforwardIso j fbar).app F

/-- The objectwise identification is the component of
`etaleLowerShriekCompactifyPushforwardIso`. -/
theorem etaleLowerShriekCompactifyPushforwardIso_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    etaleLowerShriekCompactifyPushforwardIso_app j fbar F =
      (etaleLowerShriekCompactifyPushforwardIso j fbar).app F :=
  sorry

/-- The forward map of `etaleLowerShriekCompactifyPushforwardIso` is the
compactification isomorphism whiskered with `etaleLowerShriekIso`. -/
theorem etaleLowerShriekCompactifyPushforwardIso_hom :
    (etaleLowerShriekCompactifyPushforwardIso j fbar).hom =
      (etaleLowerShriekCompactifyIso j fbar).hom ≫
        whiskerLeft (abelianExtensionByZero j) (etaleLowerShriekIso fbar).hom :=
  sorry


end AlgebraicGeometry.Scheme.Etale

end
