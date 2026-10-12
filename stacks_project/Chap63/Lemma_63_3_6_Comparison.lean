/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import stacks_project.Chap59.Lemma_59_70_4
public import stacks_project.Chap63.Lemma_63_3_4
public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion

/-!
# Compactification comparison for underived étale lower shriek

If `j : X ⟶ X̄` is an open immersion of `Y`-schemes and `X̄` is proper over
`Y`, the adjunction unit `F ⟶ (j_! F)|_X` together with covariance of
`etaleLowerShriek` along `j` supplies a canonical comparison
`f_! ⟶ f̄_! ∘ j_!`.
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

end AlgebraicGeometry.Scheme.Etale

end
