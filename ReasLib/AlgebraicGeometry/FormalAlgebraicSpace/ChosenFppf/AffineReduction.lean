/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.SheafifyYoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Reduced

/-! Affine-stage reduction for formal algebraic spaces. -/

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open CategoryTheory.Functor
open AlgebraicGeometry.ChosenBigFppfSite
open Opposite
noncomputable section
universe u v
namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace


/-- The sheaf associated to the scheme-theoretic reduction of an affine
stage. -/
def stageReduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) :=
  ChosenBigFppfSite.sheafifyYoneda.obj
    (Over.reduction
      ((Over.post 𝒮.toScheme).obj ((𝒮.bigAffineInclusion S).obj (D.obj i))))

/-- `stageReduction D i` is the sheafified slice Yoneda of the reduction of
the `i`-th affine stage. -/
theorem stageReduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] (D : Λ ⥤ 𝒮.bigAffineSite S) (i : Λ) :
    stageReduction D i =
      ChosenBigFppfSite.sheafifyYoneda.obj
        (Over.reduction
          ((Over.post 𝒮.toScheme).obj
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))) := by rfl

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
      (Over.reductionι
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
          (Over.reductionι
            ((Over.post 𝒮.toScheme).obj
              ((𝒮.bigAffineInclusion S).obj (D.obj i)))) ≫
        ChosenBigFppfSite.toSheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj (D.obj i)) ≫
        c.ι.app i ≫ e.inv := by rfl

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
    (colimitDiagram_isDirectedAffineThickeningColimit X).2.2

/-- The chosen cocone is a colimit isomorphic to `X`. -/
theorem colimitCocone_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Nonempty (IsColimit (colimitCocone X)) ∧
      Nonempty (X ≅ (colimitCocone X).pt) :=
  Classical.choose_spec (colimitDiagram_isDirectedAffineThickeningColimit X).2.2

/-- The chosen isomorphism from `X` to the point of the affine thickening
cocone. -/
def colimitIso {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : X ≅ (colimitCocone X).pt :=
  Classical.choice (colimitCocone_spec X).2

/-- The chosen stage of the affine thickening presentation. -/
def colimitStage {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : colimitIndex X :=
  Classical.choice (colimitDiagram_isDirectedAffineThickeningColimit X).1

/-- The chosen reduced thickening of an affine formal algebraic space. -/
def reductionWithι {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    Σ (Y : Sheaf (𝒮.bigTopology S) (Type (max u v))), Y ⟶ X :=
  ⟨stageReduction (colimitDiagram X) (colimitStage X),
    stageReductionι (colimitDiagram X) (colimitCocone X) (colimitIso X) (colimitStage X)⟩

/-- The reduction of an affine formal algebraic space, as the sheafified
reduction of one chosen affine stage. -/
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

/-- The chosen reduction pair is obtained at the selected affine stage. -/
theorem reductionWithι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    reductionWithι X =
      ⟨stageReduction (colimitDiagram X) (colimitStage X),
        stageReductionι (colimitDiagram X) (colimitCocone X) (colimitIso X)
          (colimitStage X)⟩ := by rfl

/-- The affine reduction is the selected stage reduction. -/
theorem reduction_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    reduction X = stageReduction (colimitDiagram X) (colimitStage X) := by rfl

/-- The affine reduction morphism is the morphism component of
`reductionWithι`. -/
theorem reductionι_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    reductionι X = (reductionWithι X).2 := by rfl

/-- The reduction of an affine formal algebraic space is a reduced algebraic
space. -/
theorem isReduced_reduction {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsReduced (reduction X) := sorry


end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
