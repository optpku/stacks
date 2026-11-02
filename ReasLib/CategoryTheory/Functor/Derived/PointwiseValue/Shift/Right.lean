/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Domain
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shifts of Pointwise Right-Derived Values

This leaf constructs the shift transport for pointwise right-derived values over an arbitrary
shift-compatible localization class.  The reindexing equivalence is public because it is useful
when comparing derived diagrams; the auxiliary cocones remain private implementation data.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.RightDerived.Value.Shift

/-- shifting the target of a right comma diagram gives the canonical equivalence
between the diagram at `X` and the diagram at `X⟦n⟧`. -/
@[stacks 05SU]
noncomputable def forwardEquivalence
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    CostructuredArrow S.Q (S.Q.obj X) ≌ CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) :=
  (Functor.asEquivalence
      (CostructuredArrow.post S.Q (shiftFunctor S.Localization n) (S.Q.obj X))).trans
    ((CostructuredArrow.mapNatIso (S.Q.commShiftIso n).symm).trans
      ((CostructuredArrow.mapIso ((S.Q.commShiftIso n).app X).symm).trans
        (CostructuredArrow.pre (shiftFunctor D n) S.Q (S.Q.obj (X⟦n⟧))).asEquivalence))

/-- the inverse right-comma reindexing functor used to compare pointwise
right-derived diagrams before and after a shift. -/
@[stacks 05SU]
noncomputable def indexFunctor
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) ⥤ CostructuredArrow S.Q (S.Q.obj X) :=
  (forwardEquivalence (S := S) X n).inverse

/-- The right-comma reindexing equivalence in the direction used by pointwise colimit
constructions.  Unlike `.symm`, its forward functor is definitionally
`indexFunctor`, which makes it suitable for transport APIs indexed by an
equivalence. -/
@[stacks 05SU]
noncomputable def indexEquivalence
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    CostructuredArrow S.Q (S.Q.obj (X⟦n⟧)) ≌ CostructuredArrow S.Q (S.Q.obj X) :=
  Equivalence.mk
    (indexFunctor (S := S) X n)
    (forwardEquivalence (S := S) X n).functor
    (forwardEquivalence (S := S) X n).counitIso.symm
    (forwardEquivalence (S := S) X n).unitIso.symm

set_option backward.isDefEq.respectTransparency false in
/-- The right-comma equivalence projects to the source shift. -/
@[stacks 05SU]
noncomputable def forwardEquivalenceProj
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    (forwardEquivalence (S := S) X n).functor ⋙
        CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ≅
      CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ shiftFunctor D n := by
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro A B f
  change (shiftFunctor D n).map f.left ≫ 𝟙 _ = 𝟙 _ ≫ (shiftFunctor D n).map f.left
  simp only [Category.comp_id, Category.id_comp]

/-- Reindexing the shifted right-comma diagram and then projecting agrees with shifting the
original projection functor. -/
@[stacks 05SU]
noncomputable def indexFunctorProj
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    indexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ shiftFunctor D n ≅
      CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) := by
  let e := forwardEquivalence (S := S) X n
  let P := CostructuredArrow.proj S.Q (S.Q.obj X)
  let P' := CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧))
  change e.inverse ⋙ P ⋙ shiftFunctor D n ≅ P'
  calc
    e.inverse ⋙ P ⋙ shiftFunctor D n ≅ e.inverse ⋙ (e.functor ⋙ P') := by
      simpa [e, P, P'] using Functor.isoWhiskerLeft e.inverse
        (forwardEquivalenceProj (S := S) X n).symm
    _ ≅ (e.inverse ⋙ e.functor) ⋙ P' :=
      (Functor.associator e.inverse e.functor P').symm
    _ ≅ (𝟭 _) ⋙ P' := Functor.isoWhiskerRight e.counitIso P'
    _ ≅ P' := Functor.leftUnitor P'

/-- the reindexed and shifted right-derived diagram is canonically isomorphic to
the literal right-derived diagram at the shifted source object. -/
@[stacks 05SU]
noncomputable def diagramIso
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) :
    indexFunctor (S := S) X n ⋙
        CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor D' n ≅
      CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F := by
  let I := indexFunctor (S := S) X n
  let P := CostructuredArrow.proj S.Q (S.Q.obj X)
  let P' := CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧))
  let G := shiftFunctor D n
  let H := shiftFunctor D' n
  change ((I ⋙ P) ⋙ F) ⋙ H ≅ P' ⋙ F
  calc
    ((I ⋙ P) ⋙ F) ⋙ H ≅ (I ⋙ P) ⋙ (F ⋙ H) :=
      Functor.associator (I ⋙ P) F H
    _ ≅ (I ⋙ P) ⋙ (G ⋙ F) := Functor.isoWhiskerLeft (I ⋙ P) (F.commShiftIso n).symm
    _ ≅ ((I ⋙ P) ⋙ G) ⋙ F :=
      (Functor.associator (I ⋙ P) G F).symm
    _ ≅ (I ⋙ (P ⋙ G)) ⋙ F := Functor.isoWhiskerRight (Functor.associator I P G) F
    _ ≅ P' ⋙ F := by
      simpa [I, P, P', G] using
        Functor.isoWhiskerRight (indexFunctorProj (S := S) X n) F

/-- The explicit cocone obtained by transporting a right-derived cocone through a source and
target shift. -/
@[stacks 05SU]
noncomputable def cocone
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) (hX : F.HasPointwiseRightDerivedFunctorAt S X) :
    Cocone (CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F) :=
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let hRX : HasColimit RX := hX.hasColimit'
  let c :
      Cocone
        (indexFunctor (S := S) X n ⋙
          CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor D' n) :=
    (shiftFunctor D' n).mapCocone
      ((@colimit.cocone _ _ _ _ RX hRX).whisker
        (indexFunctor (S := S) X n))
  (Cocone.precompose (diagramIso (F := F) (S := S) X n).inv).obj c

/-- The transported right-derived cocone is colimiting. -/
@[stacks 05SU]
noncomputable def cocone_isColimit
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) (hX : F.HasPointwiseRightDerivedFunctorAt S X) :
    IsColimit (cocone (F := F) (S := S) X n hX) := by
  let RX := CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F
  let e := indexEquivalence (S := S) X n
  let hRX : HasColimit RX := hX.hasColimit'
  let c :
      Cocone
        (indexFunctor (S := S) X n ⋙
          CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F ⋙ shiftFunctor D' n) :=
    (shiftFunctor D' n).mapCocone
      ((@colimit.cocone _ _ _ _ RX hRX).whisker
        (indexFunctor (S := S) X n))
  have hc₀ :
      IsColimit
        ((@colimit.cocone _ _ _ _ RX hRX).whisker
          (indexFunctor (S := S) X n)) := by
    change IsColimit ((@colimit.cocone _ _ _ _ RX hRX).whisker e.functor)
    exact (@colimit.isColimit _ _ _ _ RX hRX).whiskerEquivalence e
  have hc : IsColimit c := by
    change IsColimit
      ((shiftFunctor D' n).mapCocone
        ((@colimit.cocone _ _ _ _ RX hRX).whisker
          (indexFunctor (S := S) X n)))
    exact isColimitOfPreserves (shiftFunctor D' n) hc₀
  change IsColimit
    ((Cocone.precompose (diagramIso (F := F) (S := S) X n).inv).obj c)
  exact
    (IsColimit.precomposeInvEquiv (diagramIso (F := F) (S := S) X n) c).symm hc

/-- pointwise right-derived definedness is stable under every integer shift. -/
@[stacks 05SU]
instance _root_.CategoryTheory.Functor.RightDerived.Definedness.property.isStableUnderShift
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (Functor.RightDerived.Definedness.property F S) ℤ where
  isStableUnderShiftBy n :=
    { le_shift := fun X hX ↦
        ⟨⟨cocone (F := F) (S := S) X n hX,
          cocone_isColimit (F := F) (S := S) X n hX⟩⟩ }

/-- a pointwise right-derived value defined at `X` is also defined at `X⟦n⟧`. -/
@[stacks 05SU]
noncomputable instance pointwiseAt_shift
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [F.HasPointwiseRightDerivedFunctorAt S X] :
    F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) :=
  ⟨⟨cocone (F := F) (S := S) X n inferInstance,
    cocone_isColimit (F := F) (S := S) X n inferInstance⟩⟩

/-- pointwise right-derived definedness is invariant under integer shifts. -/
@[stacks 05SU]
theorem hasPointwiseAt_iff_shift
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      F.HasPointwiseRightDerivedFunctorAt S (X⟦n⟧) := by
  simpa only [Functor.RightDerived.Definedness.property] using
    ((Functor.RightDerived.Definedness.property F S).prop_shift_iff_of_isStableUnderShift X n).symm

/-- the pointwise right-derived value at `X⟦n⟧` is canonically isomorphic to the
shift of the pointwise right-derived value at `X`. -/
@[stacks 05SU]
noncomputable def valueIso
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [F.HasPointwiseRightDerivedFunctorAt S X] :
    CategoryTheory.Functor.RightDerived.Value.obj F S (X⟦n⟧) ≅ ((CategoryTheory.Functor.RightDerived.Value.obj F S X)⟦n⟧) := by
  let shifted := cocone (F := F) (S := S) X n inferInstance
  let RY := CostructuredArrow.proj S.Q (S.Q.obj (X⟦n⟧)) ⋙ F
  let hc : IsColimit shifted :=
    cocone_isColimit (F := F) (S := S) X n inferInstance
  let hRY : HasColimit RY := inferInstance
  exact (hc.coconePointUniqueUpToIso (@colimit.isColimit _ _ _ _ RY hRY)).symm

/-- The right-derived shift comparison is natural for maps between points where the two raw
right-derived values are defined. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_naturality
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y] :
    CategoryTheory.Functor.RightDerived.Value.map F S ((shiftFunctor D n).map f) ≫
        (valueIso F S Y n).hom =
      (valueIso F S X n).hom ≫
        (shiftFunctor D' n).map (CategoryTheory.Functor.RightDerived.Value.map F S f) := sorry

/-- Naturality of the inverse right-derived shift comparison. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_inv_naturality
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseRightDerivedFunctorAt S X] [F.HasPointwiseRightDerivedFunctorAt S Y] :
    (shiftFunctor D' n).map (CategoryTheory.Functor.RightDerived.Value.map F S f) ≫
        (valueIso F S Y n).inv =
      (valueIso F S X n).inv ≫
        CategoryTheory.Functor.RightDerived.Value.map F S ((shiftFunctor D n).map f) := sorry

/-- The right-derived shift comparison intertwines denominator legs with the shift comparison
of `F`. -/
@[stacks 05SU]
theorem valueIso_hom_comp_leg
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X X' : D} (s : X ⟶ X') (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    CategoryTheory.Functor.RightDerived.Value.ι F S ((shiftFunctor D n).map s) (S.shift hs n) ≫
        (valueIso F S X n).hom =
      ((F.commShiftIso n).app X').hom ≫
        (shiftFunctor D' n).map (CategoryTheory.Functor.RightDerived.Value.ι F S s hs) := sorry

/-- The inverse right-derived shift comparison intertwines shifted denominator legs with the
inverse shift comparison of `F`. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_inv_comp_leg
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X X' : D} (s : X ⟶ X') (hs : S s)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    (shiftFunctor D' n).map (CategoryTheory.Functor.RightDerived.Value.ι F S s hs) ≫
        (valueIso F S X n).inv =
      ((F.commShiftIso n).app X').inv ≫
        CategoryTheory.Functor.RightDerived.Value.ι F S ((shiftFunctor D n).map s) (S.shift hs n) := sorry

/-- The identity-denominator specialization of `valueIso_hom_comp_leg`. -/
@[stacks 05SU]
theorem valueIso_hom_comp_idLeg
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    [S.ContainsIdentities] (X : D) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
        (valueIso F S X n).hom =
      ((F.commShiftIso n).app X).hom ≫
        (shiftFunctor D' n).map (CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 X) (S.id_mem X)) := sorry

/-- The identity-denominator specialization of `valueIso_inv_comp_leg`. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_inv_comp_idLeg
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    [S.ContainsIdentities] (X : D) (n : ℤ)
    [F.HasPointwiseRightDerivedFunctorAt S X] :
    (shiftFunctor D' n).map (CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 X) (S.id_mem X)) ≫
        (valueIso F S X n).inv =
      ((F.commShiftIso n).app X).inv ≫
        CategoryTheory.Functor.RightDerived.Value.ι F S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) := sorry


end Functor.RightDerived.Value.Shift

end CategoryTheory
