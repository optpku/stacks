module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Lemma_87_12_1_Reduced

/-!
# Affine reduction of a formal algebraic space

The reduction of an affine formal algebraic space is the sheafified functor of
points, over the base, of the scheme-theoretic reduction of any affine stage.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor
open AlgebraicGeometry.ChosenBigFppfSite
open Opposite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The reduction of a scheme over a base, as an object of the slice. -/
def reductionOver {T : Scheme.{u}} (Y : Over T) : Over T :=
  Over.mk (Scheme.reductionι Y.left ≫ Y.hom)

/-- The underlying scheme of a slice reduction is the scheme-theoretic
reduction. -/
theorem reductionOver_left {T : Scheme.{u}} (Y : Over T) :
    (reductionOver Y).left = Scheme.reduction Y.left := sorry

/-- The canonical thickening from the slice reduction of a scheme over a
base. -/
def reductionOverι {T : Scheme.{u}} (Y : Over T) : reductionOver Y ⟶ Y :=
  Over.homMk (Scheme.reductionι Y.left) sorry

/-- The underlying morphism of `reductionOverι Y` is the scheme-theoretic
reduction inclusion. -/
theorem reductionOverι_left {T : Scheme.{u}} (Y : Over T) :
    (reductionOverι Y).left = Scheme.reductionι Y.left := sorry

namespace ChosenBigFppfSite

/-- The sheaf on `(Sch/S)_fppf` associated to a scheme over the image of `S`,
obtained by sheafifying Hom-spaces in the slice and lifting to
`Type (max u v)`. -/
def sheafifyYoneda {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] :
    Over (𝒮.toScheme.obj S) ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)) where
  obj Y :=
    (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).obj
      ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj Y ⋙ uliftFunctor.{v})
  map {Y Z} f :=
    (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
      (whiskerRight (whiskerLeft (Over.post 𝒮.toScheme).op (yoneda.map f))
        uliftFunctor.{v})
  map_id := sorry
  map_comp := sorry

/-- `sheafifyYoneda.obj Y` is the sheafification of the `ULift` of Hom-spaces
in the slice along `Over.post 𝒮.toScheme`. -/
theorem sheafifyYoneda_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (Y : Over (𝒮.toScheme.obj S)) :
    sheafifyYoneda.obj Y =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).obj
        ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj Y ⋙ uliftFunctor.{v}) := sorry

/-- Presheaf comparison from slice Yoneda of a site object to `uliftYoneda`. -/
def toUliftYoneda {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    (U : 𝒮.bigSite S) :
    ((Over.post 𝒮.toScheme).op ⋙ yoneda.obj ((Over.post 𝒮.toScheme).obj U) ⋙
        uliftFunctor.{v}) ⟶
      uliftYoneda.{max u v}.obj U where
  app W :=
    ↾fun f ↦
      ULift.up.{max u v, v}
        (Over.homMk (𝒮.fullyFaithful.preimage f.down.left) sorry)
  naturality := sorry

/-- Comparison from the sheafified slice Yoneda of a site object to its
sheafified representable, using full faithfulness of `𝒮.toScheme`. -/
def toSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] (U : 𝒮.bigSite S) :
    sheafifyYoneda.obj ((Over.post 𝒮.toScheme).obj U) ⟶
      (𝒮.bigTopology S).sheafifiedRepresentable U :=
  (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map (toUliftYoneda U)

/-- `toSheafifiedRepresentable U` is the sheafification of `toUliftYoneda U`. -/
theorem toSheafifiedRepresentable_spec {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] (U : 𝒮.bigSite S) :
    toSheafifiedRepresentable U =
      (presheafToSheaf (𝒮.bigTopology S) (Type (max u v))).map
        (toUliftYoneda U) := sorry

end ChosenBigFppfSite

namespace IsAffineFormalAlgebraicSpace

/-- The sheaf associated to the scheme-theoretic reduction of an affine
stage. -/
def stageReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ChosenBigFppfSite.sheafifyYoneda.obj
    (reductionOver
      ((Over.post 𝒮.toScheme).obj ((𝒮.bigAffineInclusion S).obj (D.obj i))))

/-- `stageReduction D i` is the sheafified slice Yoneda of the reduction of
the `i`-th affine stage. -/
theorem stageReduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    stageReduction D i =
      ChosenBigFppfSite.sheafifyYoneda.obj
        (reductionOver
          ((Over.post 𝒮.toScheme).obj
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))) := sorry

/-- The stage reduction inclusion into the sheaf colimit of an affine
thickening presentation. -/
def stageReductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (e : X ≅ c.pt) (i : Λ) : stageReduction D i ⟶ X :=
  ChosenBigFppfSite.sheafifyYoneda.map
      (reductionOverι
        ((Over.post 𝒮.toScheme).obj ((𝒮.bigAffineInclusion S).obj (D.obj i)))) ≫
    ChosenBigFppfSite.toSheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj (D.obj i)) ≫
    c.ι.app i ≫ e.inv

/-- `stageReductionι` is the composite of the slice reduction map, the
comparison to the sheafified representable of the stage, and the cocone leg. -/
theorem stageReductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (c : Cocone
      (D ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (e : X ≅ c.pt) (i : Λ) :
    stageReductionι D c e i =
      ChosenBigFppfSite.sheafifyYoneda.map
          (reductionOverι
            ((Over.post 𝒮.toScheme).obj
              ((𝒮.bigAffineInclusion S).obj (D.obj i)))) ≫
        ChosenBigFppfSite.toSheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj (D.obj i)) ≫
        c.ι.app i ≫ e.inv := sorry

/-- The chosen directed index of an affine thickening presentation. -/
def colimitIndex {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : Type (max u v) :=
  Classical.choose ‹IsAffineFormalAlgebraicSpace X›.exists_colimit

/-- The chosen preorder on the directed index of an affine thickening
presentation. -/
instance instPreorder_colimitIndex {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : Preorder (colimitIndex X) :=
  Classical.choose
    (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit)

/-- The chosen directedness of the index of an affine thickening
presentation. -/
instance instIsDirected_colimitIndex {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsDirected (colimitIndex X) (· ≤ ·) :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit))

/-- The chosen affine stage diagram of an affine formal algebraic space. -/
def colimitDiagram {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    colimitIndex X ⥤ 𝒮.bigAffineSite S :=
  Classical.choose
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit)))

/-- The chosen diagram is a directed affine thickening colimit of `X`. -/
theorem colimitDiagram_isDirectedAffineThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    IsDirectedAffineThickeningColimit (colimitDiagram X) X :=
  Classical.choose_spec
    (Classical.choose_spec
      (Classical.choose_spec
        (Classical.choose_spec ‹IsAffineFormalAlgebraicSpace X›.exists_colimit)))

/-- The chosen sheaf cocone of the affine thickening presentation. -/
def colimitCocone {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Cocone
      (colimitDiagram X ⋙ 𝒮.bigAffineInclusion S ⋙
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor) :=
  Classical.choose
    (colimitDiagram_isDirectedAffineThickeningColimit X).2

/-- The chosen cocone is a colimit isomorphic to `X`. -/
theorem colimitCocone_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Nonempty (IsColimit (colimitCocone X)) ∧
      Nonempty (X ≅ (colimitCocone X).pt) :=
  Classical.choose_spec (colimitDiagram_isDirectedAffineThickeningColimit X).2

/-- The chosen isomorphism from `X` to the point of the affine thickening
cocone. -/
def colimitIso {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : X ≅ (colimitCocone X).pt :=
  Classical.choice (colimitCocone_spec X).2

/-- The chosen reduced thickening of an affine formal algebraic space, as the
sheafified reduction of one chosen affine stage together with its structure
morphism, or the identity on `X` when the index is empty. -/
def reductionWithι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Σ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))), Y ⟶ X :=
  @dite _ (Nonempty (colimitIndex X)) (Classical.propDecidable _)
    (fun h ↦
      ⟨stageReduction (colimitDiagram X) (Classical.choice h),
        stageReductionι (colimitDiagram X) (colimitCocone X) (colimitIso X)
          (Classical.choice h)⟩)
    (fun _ ↦ ⟨X, 𝟙 X⟩)

/-- The reduction of an affine formal algebraic space, as the sheafified
reduction of one chosen affine stage, or `X` itself when the index is empty. -/
def reduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  (reductionWithι X).1

/-- The canonical morphism from the reduction of an affine formal algebraic
space. -/
def reductionι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    reduction X ⟶ X :=
  (reductionWithι X).2

/-- The chosen reduced thickening is `stageReduction`/`stageReductionι` of
`colimitDiagram`, `colimitCocone`, `colimitIso`, and a chosen index, or the
identity on `X` when that index is empty. -/
theorem reductionWithι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    reductionWithι X =
      @dite (Σ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))), Y ⟶ X)
        (Nonempty (colimitIndex X)) (Classical.propDecidable _)
        (fun h ↦
          ⟨stageReduction (colimitDiagram X) (Classical.choice h),
            stageReductionι (colimitDiagram X) (colimitCocone X) (colimitIso X)
              (Classical.choice h)⟩)
        (fun _ ↦ ⟨X, 𝟙 X⟩) := sorry

/-- The affine reduction is `stageReduction` of the chosen diagram and stage,
or `X` when the index is empty. -/
theorem reduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (∀ h : Nonempty (colimitIndex X),
        reduction X = stageReduction (colimitDiagram X) (Classical.choice h)) ∧
      (¬ Nonempty (colimitIndex X) → reduction X = X) := sorry

/-- The affine reduction morphism is the morphism component of
`reductionWithι`. -/
theorem reductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    reductionι X = (reductionWithι X).2 := sorry

/-- The reduction of an affine formal algebraic space is a reduced algebraic
space. -/
instance instIsReduced_reduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsReduced (reduction X) := sorry

end IsAffineFormalAlgebraicSpace

end AlgebraicGeometry
