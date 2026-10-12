/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Definition_67_13_2_InverseImage
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap81.«81_10_6_1_Glueing»

/-!
# Formal glueing of algebraic spaces

The category `Spaces(Y → X, Z)` of diagrams `U' ← V' → Y'` with both squares
cartesian is the categorical pullback of `Over.pullback` along `f|_V : V ⟶ U`
and along `j' : V ⟶ Y`. The canonical functor `Spaces/X ⥤ Spaces(Y → X, Z)`
sends `X' ⟶ X` to `U ×_X X' ← V ×_X X' → Y ×_X X'`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QCoh.FormalGlueing (restrict restrict_comp)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormalGlueing

/-- The category `Spaces(Y → X, Z)` of triples `(U', Y', φ)` with `U'` an
algebraic space over `U = X \ Z`, `Y'` an algebraic space over `Y`, and
`φ : U' ×_U V ≅ Y' ×_Y V` on `V = Y \ f⁻¹Z`. -/
abbrev category {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :=
  CategoricalPullback (Over.pullback (restrict f i))
    (Over.pullback (closedImmersionComplementι (inverseImageι f i)))

/-- The canonical isomorphism `(U ×_X X') ×_U V ≅ (Y ×_X X') ×_Y V`. -/
def can {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    Over.pullback (closedImmersionComplementι i) ⋙ Over.pullback (restrict f i) ≅
      Over.pullback f ⋙
        Over.pullback (closedImmersionComplementι (inverseImageι f i)) :=
  (Over.pullbackComp (restrict f i) (closedImmersionComplementι i)).symm ≪≫
    eqToIso (congrArg (fun h ↦ Over.pullback h) (restrict_comp f i)) ≪≫
    Over.pullbackComp (closedImmersionComplementι (inverseImageι f i)) f

/-- The canonical functor `Spaces/X ⥤ Spaces(Y → X, Z)` sending `X' ⟶ X` to
`(U ×_X X', Y ×_X X', can)`. -/
def functor {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Over X ⥤ category f i :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (Over.pullback (restrict f i))
      (Over.pullback (closedImmersionComplementι (inverseImageι f i)))
      (Over X)).obj
    { fst := Over.pullback (closedImmersionComplementι i)
      snd := Over.pullback f
      iso := can f i }

/-- An object of `Spaces(Y → X, Z)` from a triple `(U', Y', φ)`. -/
def mk {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] {U' : Over (closedImmersionComplement i)}
    {Y' : Over Y}
    (φ : (Over.pullback (restrict f i)).obj U' ≅
      (Over.pullback (closedImmersionComplementι (inverseImageι f i))).obj Y') :
    category f i :=
  ⟨U', Y', φ⟩

/-- The overlap space `V'` of an object of `Spaces(Y → X, Z)`, recovered as the
pullback of `U'` along `f|_V`. -/
def overlap {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (obj : category f i) :
    Over (closedImmersionComplement (inverseImageι f i)) :=
  (Over.pullback (restrict f i)).obj obj.fst

/-- The first component of the canonical glueing functor is base change along
`j : U ⟶ X`. -/
theorem obj_fst {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (X' : Over X) :
    ((functor f i).obj X').fst =
      (Over.pullback (closedImmersionComplementι i)).obj X' :=
  sorry

/-- The second component of the canonical glueing functor is base change along
`f`. -/
theorem obj_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (X' : Over X) :
    ((functor f i).obj X').snd = (Over.pullback f).obj X' :=
  sorry

/-- The structural isomorphism of the canonical glueing functor is the component
of `can`. -/
theorem obj_iso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (X' : Over X) :
    ((functor f i).obj X').iso = (can f i).app X' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormalGlueing
