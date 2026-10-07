module

public import stacks_project.Chap63.Lemma_63_3_6_Comparison

/-!
# Compactification of underived étale lower shriek

Lemma 63.3.6: if `j : X ⟶ X̄` is an open immersion of schemes over `Y` with
`X̄` proper over `Y`, then `f_! ≅ f̄_! ∘ j_!`, and hence `f_! ≅ f̄_* ∘ j_!`
as functors on abelian small-étale sheaves.
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

/-- Lemma 63.3.6 (1): Let `Y` be a scheme. Let `j : X ⟶ X̄` be an open
immersion of schemes over `Y` with `X̄` proper over `Y`. Denote `f : X ⟶ Y`
and `f̄ : X̄ ⟶ Y` the structure morphisms. For `F` in `Ab(X_étale)` there is
a canonical isomorphism `f_! F ⟶ f̄_! (j_! F)`. -/
@[stacks 0F52]
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

/-- Lemma 63.3.6 (2): Let `Y` be a scheme. Let `j : X ⟶ X̄` be an open
immersion of schemes over `Y` with `X̄` proper over `Y`. Denote `f : X ⟶ Y`
and `f̄ : X̄ ⟶ Y` the structure morphisms. As `f̄_! = f̄_*` by Lemma 63.3.4
we obtain `f̄_* ∘ j_! = f_!` as functors `Ab(X_étale) ⟶ Ab(Y_étale)`. -/
@[stacks 0F52]
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
