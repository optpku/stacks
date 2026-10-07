module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap61.Lemma_61_12_19_SmallToBig

/-!
# Abelian inverse image along pro-étale relocalization

This leaf owns the abelian sheaf functor `iInverseImage` induced by small-to-big
pro-étale relocalization.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Inverse image on abelian sheaves along pro-étale relocalization from the big
site over `S` to the small pro-étale site of `T`. -/
abbrev iInverseImage :
    Sheaf (proetaleTopology.over S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T) AddCommGrpCat.{u + 1} :=
  (SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
    AddCommGrpCat.{u + 1} (topology T) (proetaleTopology.over S)

/-- Inverse image on abelian sheaves is continuous sheaf pushforward along
pro-étale relocalization. -/
theorem iInverseImage_eq :
    iInverseImage f =
      (SmallToBig.relocalizationFunctor f).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1} (topology T) (proetaleTopology.over S) := sorry

end AlgebraicGeometry.Scheme.ProEt

