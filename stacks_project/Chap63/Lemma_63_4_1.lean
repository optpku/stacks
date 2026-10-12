/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_4_1_Comparison

/-!
# Identification of finite-support and compact-support lower shriek

Lemma 63.4.1: if `f : X ⟶ Y` is separated and locally quasi-finite, then
functorially in abelian étale sheaves `F` on `X` there is a canonical
isomorphism of abelian presheaves `f_{p!} F ≅ f_! F` identifying the sheaf
`f_! F` of Definition 63.3.3 with the presheaf `f_{p!} F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [IsSeparated f] [LocallyQuasiFinite f] [LocallyOfFiniteType f]

/-- Lemma 63.4.1: Let `f : X ⟶ Y` be a separated and locally quasi-finite
morphism of schemes. Functorially in `F` in `Ab(X_étale)` there is a canonical
isomorphism `f_{p!} F ⟶ f_! F` of abelian presheaves which identifies the sheaf
`f_! F` of Definition 63.3.3 with the presheaf `f_{p!} F`. -/
@[stacks 0F6N]
def lowerShriekPresheafIso :
    lowerShriekPresheaf f ≅
      etaleLowerShriek f ⋙
        sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u} where
  hom := lowerShriekPresheafComparison f
  inv := lowerShriekPresheafComparisonInv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identification of Lemma 63.4.1 at an abelian étale sheaf `F`. -/
def lowerShriekPresheafIso_app
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriekPresheaf f).obj F ≅
      (sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj
        ((etaleLowerShriek f).obj F) :=
  (lowerShriekPresheafIso f).app F

/-- The objectwise identification is the component of `lowerShriekPresheafIso`. -/
theorem lowerShriekPresheafIso_app_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    lowerShriekPresheafIso_app f F = (lowerShriekPresheafIso f).app F :=
  sorry

/-- The forward map of `lowerShriekPresheafIso` is the zero-extension
comparison. -/
theorem lowerShriekPresheafIso_hom :
    (lowerShriekPresheafIso f).hom = lowerShriekPresheafComparison f :=
  sorry

/-- The inverse map of `lowerShriekPresheafIso` is the colimit-coprojection
comparison. -/
theorem lowerShriekPresheafIso_inv :
    (lowerShriekPresheafIso f).inv = lowerShriekPresheafComparisonInv f :=
  sorry

/-- After the identification of Lemma 63.4.1, the presheaf `f_{p!} F` is a sheaf
on `Y_étale`. -/
theorem lowerShriekPresheaf_isSheaf
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    Presheaf.IsSheaf Y.smallEtaleTopology ((lowerShriekPresheaf f).obj F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
