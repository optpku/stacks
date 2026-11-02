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
# Shifts of Pointwise Left-Derived Values

This leaf is the left-derived counterpart of `PointwiseValue.Shift.Right`.  It constructs the shift
transport for pointwise limit presentations over an arbitrary shift-compatible localization
class, while exposing only the reindexing and comparison API useful to consumers.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits MorphismProperty ObjectProperty

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

namespace Functor.LeftDerived.Value.Shift

/-- shifting the target of a left comma diagram gives the canonical equivalence
between the diagram at `X` and the diagram at `X⟦n⟧`. -/
@[stacks 05SU]
noncomputable def forwardEquivalence
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    StructuredArrow (S.Q.obj X) S.Q ≌ StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q :=
  (Functor.asEquivalence
      (StructuredArrow.post (S.Q.obj X) S.Q (shiftFunctor S.Localization n))).trans
    ((StructuredArrow.mapNatIso (S.Q.commShiftIso n).symm).trans
      ((StructuredArrow.mapIso ((S.Q.commShiftIso n).app X).symm).trans
        (StructuredArrow.pre (S.Q.obj (X⟦n⟧)) (shiftFunctor D n) S.Q).asEquivalence))

/-- the inverse left-comma reindexing functor used to compare pointwise
left-derived diagrams before and after a shift. -/
@[stacks 05SU]
noncomputable def indexFunctor
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q ⥤ StructuredArrow (S.Q.obj X) S.Q :=
  (forwardEquivalence (S := S) X n).inverse

/-- The left-comma reindexing equivalence in the direction used by pointwise limit
constructions.  Unlike `.symm`, its forward functor is definitionally
`indexFunctor`, which makes it suitable for transport APIs indexed by an
equivalence. -/
@[stacks 05SU]
noncomputable def indexEquivalence
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    StructuredArrow (S.Q.obj (X⟦n⟧)) S.Q ≌ StructuredArrow (S.Q.obj X) S.Q :=
  Equivalence.mk
    (indexFunctor (S := S) X n)
    (forwardEquivalence (S := S) X n).functor
    (forwardEquivalence (S := S) X n).counitIso.symm
    (forwardEquivalence (S := S) X n).unitIso.symm

set_option backward.isDefEq.respectTransparency false in
/-- The left-comma equivalence projects to the source shift. -/
@[stacks 05SU]
noncomputable def forwardEquivalenceProj
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    (forwardEquivalence (S := S) X n).functor ⋙
        StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ≅
      StructuredArrow.proj (S.Q.obj X) S.Q ⋙ shiftFunctor D n := by
  refine NatIso.ofComponents (fun _ ↦ Iso.refl _) ?_
  intro A B f
  change (shiftFunctor D n).map f.right ≫ 𝟙 _ = 𝟙 _ ≫ (shiftFunctor D n).map f.right
  simp only [Category.comp_id, Category.id_comp]

/-- Reindexing the shifted left-comma diagram and then projecting agrees with shifting the
original projection functor. -/
@[stacks 05SU]
noncomputable def indexFunctorProj
    [HasShift D ℤ] [S.IsCompatibleWithShift ℤ] (X : D) (n : ℤ) :
    indexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ shiftFunctor D n ≅
      StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q := by
  let e := forwardEquivalence (S := S) X n
  let P := StructuredArrow.proj (S.Q.obj X) S.Q
  let P' := StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q
  change e.inverse ⋙ P ⋙ shiftFunctor D n ≅ P'
  calc
    e.inverse ⋙ P ⋙ shiftFunctor D n ≅ e.inverse ⋙ (e.functor ⋙ P') := by
      simpa [e, P, P'] using Functor.isoWhiskerLeft e.inverse
        (forwardEquivalenceProj (S := S) X n).symm
    _ ≅ (e.inverse ⋙ e.functor) ⋙ P' :=
      (Functor.associator e.inverse e.functor P').symm
    _ ≅ (𝟭 _) ⋙ P' := Functor.isoWhiskerRight e.counitIso P'
    _ ≅ P' := Functor.leftUnitor P'

/-- the reindexed and shifted left-derived diagram is canonically isomorphic to
the literal left-derived diagram at the shifted source object. -/
@[stacks 05SU]
noncomputable def diagramIso
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) :
    indexFunctor (S := S) X n ⋙
        StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor D' n ≅
      StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F := by
  let I := indexFunctor (S := S) X n
  let P := StructuredArrow.proj (S.Q.obj X) S.Q
  let P' := StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q
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

/-- The explicit cone obtained by transporting a left-derived cone through a source and target
shift. -/
@[stacks 05SU]
noncomputable def cone
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) (hX : F.HasPointwiseLeftDerivedFunctorAt S X) :
    Cone (StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F) :=
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let hLX : HasLimit LX := hX.hasLimit'
  let c :
      Cone
        (indexFunctor (S := S) X n ⋙
          StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor D' n) :=
    (shiftFunctor D' n).mapCone
      ((@limit.cone _ _ _ _ LX hLX).whisker
        (indexFunctor (S := S) X n))
  (Cone.postcompose (diagramIso (F := F) (S := S) X n).hom).obj c

/-- The transported left-derived cone is limiting. -/
@[stacks 05SU]
noncomputable def cone_isLimit
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) (hX : F.HasPointwiseLeftDerivedFunctorAt S X) :
    IsLimit (cone (F := F) (S := S) X n hX) := by
  let LX := StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F
  let e := indexEquivalence (S := S) X n
  let hLX : HasLimit LX := hX.hasLimit'
  let c :
      Cone
        (indexFunctor (S := S) X n ⋙
          StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F ⋙ shiftFunctor D' n) :=
    (shiftFunctor D' n).mapCone
      ((@limit.cone _ _ _ _ LX hLX).whisker
        (indexFunctor (S := S) X n))
  have hc₀ :
      IsLimit
        ((@limit.cone _ _ _ _ LX hLX).whisker
          (indexFunctor (S := S) X n)) := by
    change IsLimit ((@limit.cone _ _ _ _ LX hLX).whisker e.functor)
    exact (@limit.isLimit _ _ _ _ LX hLX).whiskerEquivalence e
  have hc : IsLimit c := by
    change IsLimit
      ((shiftFunctor D' n).mapCone
        ((@limit.cone _ _ _ _ LX hLX).whisker
          (indexFunctor (S := S) X n)))
    exact isLimitOfPreserves (shiftFunctor D' n) hc₀
  change IsLimit
    ((Cone.postcompose (diagramIso (F := F) (S := S) X n).hom).obj c)
  exact
    (IsLimit.postcomposeHomEquiv (diagramIso (F := F) (S := S) X n) c).symm hc

/-- pointwise left-derived definedness is stable under every integer shift. -/
@[stacks 05SU]
instance _root_.CategoryTheory.Functor.LeftDerived.Definedness.property.isStableUnderShift
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ] :
    IsStableUnderShift (Functor.LeftDerived.Definedness.property F S) ℤ where
  isStableUnderShiftBy n :=
    { le_shift := fun X hX ↦
        ⟨⟨cone (F := F) (S := S) X n hX,
          cone_isLimit (F := F) (S := S) X n hX⟩⟩ }

/-- a pointwise left-derived value defined at `X` is also defined at `X⟦n⟧`. -/
@[stacks 05SU]
noncomputable instance pointwiseAt_shift
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) :=
  ⟨⟨cone (F := F) (S := S) X n inferInstance,
    cone_isLimit (F := F) (S := S) X n inferInstance⟩⟩

/-- pointwise left-derived definedness is invariant under integer shifts. -/
@[stacks 05SU]
theorem hasPointwiseAt_iff_shift
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      F.HasPointwiseLeftDerivedFunctorAt S (X⟦n⟧) := by
  simpa only [Functor.LeftDerived.Definedness.property] using
    ((Functor.LeftDerived.Definedness.property F S).prop_shift_iff_of_isStableUnderShift X n).symm

/-- the pointwise left-derived value at `X⟦n⟧` is canonically isomorphic to the
shift of the pointwise left-derived value at `X`. -/
@[stacks 05SU]
noncomputable def valueIso
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (X : D) (n : ℤ) [F.HasPointwiseLeftDerivedFunctorAt S X] :
    CategoryTheory.Functor.LeftDerived.Value.obj F S (X⟦n⟧) ≅ ((CategoryTheory.Functor.LeftDerived.Value.obj F S X)⟦n⟧) := by
  let shifted := cone (F := F) (S := S) X n inferInstance
  let LY := StructuredArrow.proj (S.Q.obj (X⟦n⟧)) S.Q ⋙ F
  let hc : IsLimit shifted :=
    cone_isLimit (F := F) (S := S) X n inferInstance
  let hLY : HasLimit LY := inferInstance
  exact (hc.conePointUniqueUpToIso (@limit.isLimit _ _ _ _ LY hLY)).symm

/-- The left-derived shift comparison is natural for maps between points where the two raw
left-derived values are defined. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_naturality
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    CategoryTheory.Functor.LeftDerived.Value.map F S ((shiftFunctor D n).map f) ≫
        (valueIso F S Y n).hom =
      (valueIso F S X n).hom ≫
        (shiftFunctor D' n).map (CategoryTheory.Functor.LeftDerived.Value.map F S f) := sorry

/-- Naturality of the inverse left-derived shift comparison. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_inv_naturality
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X Y : D} (f : X ⟶ Y)
    [F.HasPointwiseLeftDerivedFunctorAt S X] [F.HasPointwiseLeftDerivedFunctorAt S Y] :
    (shiftFunctor D' n).map (CategoryTheory.Functor.LeftDerived.Value.map F S f) ≫
        (valueIso F S Y n).inv =
      (valueIso F S X n).inv ≫
        CategoryTheory.Functor.LeftDerived.Value.map F S ((shiftFunctor D n).map f) := sorry

/-- The left-derived shift comparison intertwines denominator projections with the shift
comparison of `F`. -/
@[stacks 05SU]
theorem valueIso_hom_comp_projection
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X X' : D} (s : X' ⟶ X) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    (valueIso F S X n).hom ≫
        (shiftFunctor D' n).map (CategoryTheory.Functor.LeftDerived.Value.π F S s hs) =
      CategoryTheory.Functor.LeftDerived.Value.π F S ((shiftFunctor D n).map s) (S.shift hs n) ≫
        ((F.commShiftIso n).app X').hom := sorry

/-- The inverse left-derived shift comparison intertwines shifted denominator projections with
the inverse shift comparison of `F`. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_inv_comp_projection
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    (n : ℤ) {X X' : D} (s : X' ⟶ X) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    (valueIso F S X n).inv ≫
        CategoryTheory.Functor.LeftDerived.Value.π F S ((shiftFunctor D n).map s) (S.shift hs n) =
      (shiftFunctor D' n).map (CategoryTheory.Functor.LeftDerived.Value.π F S s hs) ≫
        ((F.commShiftIso n).app X').inv := sorry

/-- The identity-denominator specialization of
`valueIso_hom_comp_projection`. -/
@[stacks 05SU]
theorem valueIso_hom_comp_idProjection
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    [S.ContainsIdentities] (X : D) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    (valueIso F S X n).hom ≫
        (shiftFunctor D' n).map (CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 X) (S.id_mem X)) =
      CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) ≫
        ((F.commShiftIso n).app X).hom := sorry

/-- The identity-denominator specialization of `valueIso_inv_comp_projection`. -/
@[reassoc (attr := simp), stacks 05SU]
theorem valueIso_inv_comp_idProjection
    [HasShift D ℤ] [HasShift D' ℤ] [F.CommShift ℤ] [S.IsCompatibleWithShift ℤ]
    [S.ContainsIdentities] (X : D) (n : ℤ)
    [F.HasPointwiseLeftDerivedFunctorAt S X] :
    (valueIso F S X n).inv ≫
        CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 (X⟦n⟧)) (S.id_mem (X⟦n⟧)) =
      (shiftFunctor D' n).map
          (CategoryTheory.Functor.LeftDerived.Value.π F S (𝟙 X) (S.id_mem X)) ≫
        ((F.commShiftIso n).app X).inv := sorry


end Functor.LeftDerived.Value.Shift

end CategoryTheory
