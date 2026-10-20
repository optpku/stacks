/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-! # Formal glueing of quasi-coherent modules -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing

/-- The category of triples `(H, G, φ)` with `H` quasi-coherent on `U = X \ Z`,
`G` quasi-coherent on `Y`, and `φ : (f|_V)^* H ≅ G|_V` on `V = Y \ f⁻¹Z`. -/
abbrev category {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :=
  CategoricalPullback (pullback (restrictToComplement f i))
    (pullback (closedImmersionComplementι (inverseImageι f i)))

/-- The canonical comparison `(f|_V)^* (F|_U) ≅ (f^* F)|_V` of quasi-coherent
pullbacks on the complement of the inverse image of a closed subspace. -/
def can {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    pullback (closedImmersionComplementι i) ⋙ pullback (restrictToComplement f i) ≅
      pullback f ⋙ pullback (closedImmersionComplementι (inverseImageι f i)) :=
  QCoh.pullbackCompIso (closedImmersionComplementι i) (restrictToComplement f i) ≪≫
    eqToIso (congrArg QCoh.pullback (restrictToComplement_comp f i)) ≪≫
    (QCoh.pullbackCompIso f (closedImmersionComplementι (inverseImageι f i))).symm

/-- The canonical functor sending a quasi-coherent module `F` on `X` to its
restriction to `U`, its pullback to `Y`, and their canonical comparison on `V`. -/
def functor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    QCoh X ⥤ category f i :=
  (CatCommSqOver.toFunctorToCategoricalPullback
      (pullback (restrictToComplement f i))
      (pullback (closedImmersionComplementι (inverseImageι f i)))
      (QCoh X)).obj
    { fst := pullback (closedImmersionComplementι i)
      snd := pullback f
      iso := can f i }

/-- The first component of the canonical glueing functor is restriction along `U ⟶ X`. -/
theorem obj_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (F : QCoh X) :
    ((functor f i).obj F).fst = (pullback (closedImmersionComplementι i)).obj F :=
  sorry

/-- The second component of the canonical glueing functor is pullback along `f`. -/
theorem obj_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (F : QCoh X) :
    ((functor f i).obj F).snd = (pullback f).obj F :=
  sorry

/-- The structural isomorphism of the canonical glueing functor is the component
of the canonical overlap comparison. -/
theorem obj_iso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (F : QCoh X) :
    ((functor f i).obj F).iso = (can f i).app F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing
