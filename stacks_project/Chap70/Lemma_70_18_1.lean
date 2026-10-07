module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap70.Lemma_70_18_1_FinitePresentationOver
public import stacks_project.Chap70.Lemma_70_18_1_BaseChange

/-!
# Glueing algebraic spaces of finite presentation along two opens

If `S = U ∪ W` is an open covering of a scheme, base change gives an equivalence
from algebraic spaces of finite presentation over `S` to the 2-fibre product of
those over `U` and over `W` above those over `U ∩ W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoricalPullback
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

variable {S : Scheme.{u}}

/-- The commutative square of finite-presentation base-change functors associated
to a pair of opens `U, W ⊆ S`. -/
def glueSquare (U W : S.Opens) :
    CatCommSqOver
      (baseChange (S.homOfLE (inf_le_left : U ⊓ W ≤ U)))
      (baseChange (S.homOfLE (inf_le_right : U ⊓ W ≤ W)))
      (FinitePresentationOver S) where
  fst := baseChange U.ι
  snd := baseChange W.ι
  iso :=
    (compIso (S.homOfLE (inf_le_left : U ⊓ W ≤ U)) U.ι).symm ≪≫
      eqToIso (congrArg (fun g : (U ⊓ W).toScheme ⟶ S ↦ baseChange g)
        (Scheme.homOfLE_ι S (inf_le_left : U ⊓ W ≤ U))) ≪≫
      (eqToIso (congrArg (fun g : (U ⊓ W).toScheme ⟶ S ↦ baseChange g)
        (Scheme.homOfLE_ι S (inf_le_right : U ⊓ W ≤ W)))).symm ≪≫
      compIso (S.homOfLE (inf_le_right : U ⊓ W ≤ W)) W.ι

/-- The functor `FP_S ⥤ FP_U ×_{FP_{U ∩ W}} FP_W` given by base change. -/
def glueFunctor (U W : S.Opens) :
    FinitePresentationOver S ⥤
      (baseChange (S.homOfLE (inf_le_left : U ⊓ W ≤ U))) ⊡
        (baseChange (S.homOfLE (inf_le_right : U ⊓ W ≤ W))) :=
  (glueSquare U W).comparison

/-- Projecting the glue comparison to the first factor recovers base change along
`U.ι`. -/
def glueFunctor_fst (U W : S.Opens) :
    glueFunctor U W ⋙
        π₁ (baseChange (S.homOfLE (inf_le_left : U ⊓ W ≤ U)))
          (baseChange (S.homOfLE (inf_le_right : U ⊓ W ≤ W))) ≅
      baseChange U.ι :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Projecting the glue comparison to the second factor recovers base change along
`W.ι`. -/
def glueFunctor_snd (U W : S.Opens) :
    glueFunctor U W ⋙
        π₂ (baseChange (S.homOfLE (inf_le_left : U ⊓ W ≤ U)))
          (baseChange (S.homOfLE (inf_le_right : U ⊓ W ≤ W))) ≅
      baseChange W.ι :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) sorry

/-- Lemma 70.18.1: if `S = U ∪ W` is an open covering of a scheme, then the
functor `FP_S ⥤ FP_U ×_{FP_{U ∩ W}} FP_W` given by base change is an
equivalence, where `FP_T` is the category of algebraic spaces of finite
presentation over `T`. -/
@[stacks 0E8Z]
theorem glueFunctor_isEquivalence (U W : S.Opens) (hcover : U ⊔ W = ⊤) :
    (glueFunctor U W).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver

