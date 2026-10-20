module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.InverseSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 59.86.3 (1): Set-valued étale base change passes to the colimit sheaf on the limit square. -/
@[stacks 0EZT] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.etaleBaseChange_of_inverseSystem :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : InverseSystemCartesianSquare I)
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DX hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DY hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DS hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DT hij)]
    [∀ i : I, QuasiCompact (C.g i)] [∀ i : I, QuasiSeparated (C.g i)]
    (Fsys : SheafSystem (orderDualToPreorderInverseSystem C.DT))
    [HasColimit (setInverseImageDiagram C.DT C.cT Fsys)]
    (h_stage : ∀ i : I,
      IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap
        (C.f i) (C.h i) (C.e i) (C.g i) (C.stage_isPullback i) (Fsys.obj i))),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap C.fLim C.hLim C.eLim C.gLim C.limit_isPullback
      (setColimitInverseImage C.DT C.cT Fsys)))

/- Lemma 59.86.3 (2): Degree-q abelian étale base change passes to the colimit sheaf on the limit square. -/
@[stacks 0EZT] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.etaleHigherDirectImageBaseChange_of_inverseSystem :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (C : InverseSystemCartesianSquare I)
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DX hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DY hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DS hij)]
    [∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap C.DT hij)]
    [∀ i : I, QuasiCompact (C.g i)] [∀ i : I, QuasiSeparated (C.g i)]
    (Fsys : AbelianSheafSystem.{u, u + 1} C.DT)
    [HasColimit (inverseImageDiagram.{u, u + 1} C.DT C.cT Fsys)] (q : ℕ)
    (h_stage : ∀ i : I,
      IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap (C.f i) (C.h i) (C.e i) (C.g i)
        (C.stage_isPullback i) q (Fsys.obj i))),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.higherMap C.fLim C.hLim C.eLim C.gLim C.limit_isPullback q
      (colimitInverseImage.{u, u + 1} C.DT C.cT Fsys)))
