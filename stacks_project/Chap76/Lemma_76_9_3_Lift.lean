module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# Open subspaces along thickenings of algebraic spaces

A thickening `i : X ⟶ X'` of algebraic spaces lifts an open subspace `U ⊂ X`
to the canonical open subspace of `X'` cut out by the image of `|U|` under
`Points.map i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

/-- The morphism `ofOver V.unop ⟶ X` associated to a section of the functor of
points. -/
def homOfSection {S : Scheme.{u}} {X : AlgebraicSpace S} {V : (Over S)ᵒᵖ}
    (φ : X.functorOfPoints.obj V) : ofOver V.unop ⟶ X :=
  yonedaEquiv.symm φ

/-- `homOfSection φ` is the Yoneda transpose of a section of the functor of points. -/
theorem homOfSection_eq {S : Scheme.{u}} {X : AlgebraicSpace S} {V : (Over S)ᵒᵖ}
    (φ : X.functorOfPoints.obj V) :
    homOfSection φ = yonedaEquiv.symm φ :=
  sorry

/-- The subfunctor of maps into `X'` whose image of points lands in the image of
`|U|` under `Points.map (U.ι ≫ i)`. -/
def extendSubfunctor {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) :
    Subfunctor X'.functorOfPoints where
  obj V := {φ | Set.range (Points.map (homOfSection φ)) ⊆
    Set.range (Points.map (U.ι ≫ i))}
  map := sorry

/-- The algebraic space underlying the open subspace of `X'` lifting `U ⊂ X`
along a thickening `i`. -/
def extendSpace {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) : AlgebraicSpace S :=
  ofFunctor (extendSubfunctor i U).toFunctor sorry sorry sorry

/-- The inclusion of `extendSpace i U` into `X'`. -/
def extendι {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) :
    extendSpace i U ⟶ X' :=
  (extendSubfunctor i U).ι

/-- The inclusion `extendι i U` is an open immersion. -/
instance instIsOpenImmersion_extendι {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) :
    IsOpenImmersion (extendι i U) :=
  sorry

/-- The canonical open subspace of `X'` lifting `U ⊂ X` along a thickening
`i : X ⟶ X'`, cut out by the image of `|U|` under `Points.map i`. -/
noncomputable def extend {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) : OpenSubspace X' :=
  ofι (extendι i U)

/-- The underlying point-set of `extend i U` is the image of the point-set of
`U` under `Points.map i`. -/
theorem extend_pointsSet {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) :
    Set.range (Points.map (extend i U).ι) =
      Points.map i '' Set.range (Points.map U.ι) :=
  sorry

/-- The open subspace `U ⊂ X` is the fibre product of `X` and `extend i U`
over `X'`. -/
theorem exists_isPullback_extend {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) :
    ∃ g : U.X ⟶ (extend i U).X, IsPullback U.ι g i (extend i U).ι :=
  sorry

/-- An open subspace of `X'` whose fibre product with `X` recovers `U` lifts
uniquely over `X'` to `extend i U`. -/
theorem unique_hom_extend {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] (U : OpenSubspace X) (V' : OpenSubspace X')
    (hV' : ∃ g : U.X ⟶ V'.X, IsPullback U.ι g i V'.ι) :
    ∃! φ : V'.X ⟶ (extend i U).X, φ ≫ (extend i U).ι = V'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace

