module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.BaseChange
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-! # Base change of the completion-functor source and target categories -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace.completionAlong

universe u

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChange_mem :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T),
    locallyOfFiniteTypeIsoOverOpenProperty
        (openComplementι X1 (T.preimage (Points.continuous_map h)))
        ((overPullback h).obj Y.obj))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChange :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)),
    Source X T ⥤ Source X1 (T.preimage (Points.continuous_map h)))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChange_obj :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T),
    ((sourceBaseChange h T).obj Y).obj = Over.mk (overPullbackSnd h Y.obj))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.sourceBaseChange_hom :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y'),
    ((sourceBaseChange h T).map φ).hom.left = overPullbackMap h φ.hom)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.targetBaseChange_mem :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T),
    FormalAlgebraicSpace.isLocallyNoetherianRigEtaleOver
        (completionAlong X1 (T.preimage (Points.continuous_map h)))
        ((Over.pullback (map h T)).obj W.obj))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.targetBaseChange :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)),
    Target X T ⥤ Target X1 (T.preimage (Points.continuous_map h)))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.targetBaseChange_obj :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T),
    ((targetBaseChange h T).obj W).obj.hom = pullback.snd W.obj.hom (map h T))

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.targetBaseChange_hom :
  ∀ {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {W W' : Target X T} (ψ : W ⟶ W'),
    ((targetBaseChange h T).map ψ).hom = (Over.pullback (map h T)).map ψ.hom)
