/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CartesianSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseSystem
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map

/-!
# Étale base change along affine-transition inverse systems

Stagewise base-change isomorphisms pass to the colimit of inverse images of the
coefficient sheaves on the limit cartesian square.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.Etale.BaseChange

/-- For a directed inverse system of cartesian scheme squares with affine transitions
and quasi-compact quasi-separated stage maps `g_i`, set-valued étale base-change
isomorphisms at every stage induce a base-change isomorphism for the colimit sheaf. -/
theorem etaleBaseChange_of_inverseSystem
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
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
      IsIso (setMap (C.f i) (C.h i) (C.e i) (C.g i) (C.stage_isPullback i) (Fsys.obj i))) :
    IsIso (setMap C.fLim C.hLim C.eLim C.gLim C.limit_isPullback
      (setColimitInverseImage C.DT C.cT Fsys)) := sorry

/-- For a directed inverse system of cartesian scheme squares with affine transitions
and quasi-compact quasi-separated stage maps `g_i`, degree-`q` abelian étale
base-change isomorphisms at every stage induce one for the colimit sheaf. -/
theorem etaleHigherDirectImageBaseChange_of_inverseSystem
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
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
      IsIso (higherMap (C.f i) (C.h i) (C.e i) (C.g i)
        (C.stage_isPullback i) q (Fsys.obj i))) :
    IsIso (higherMap C.fLim C.hLim C.eLim C.gLim C.limit_isPullback q
      (colimitInverseImage.{u, u + 1} C.DT C.cT Fsys)) := sorry

end AlgebraicGeometry.Scheme.Etale.BaseChange
