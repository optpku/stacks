/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleCover

/-!
# Affine étale locality of rig-flat morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Rig-flatness of an arrow of affine formal algebraic spaces, with the formal
and affine hypotheses supplied explicitly. -/
def isRigFlatArrow {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) : Prop :=
  @AffineFormalAlgebraicSpace.RigFlat S U V hU hUaff hV hVaff g

/-- Rig-flatness with explicit formal and affine hypotheses is equivalent to
the canonical affine rig-flatness predicate. -/
theorem isRigFlatArrow_iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) :
    isRigFlatArrow hU hUaff hV hVaff g ↔
      @AffineFormalAlgebraicSpace.RigFlat S U V hU hUaff hV hVaff g :=
  Iff.rfl

namespace RigFlat

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Every commutative square over a morphism with affine formal sources and
representable étale vertical maps has a rig-flat top arrow. -/
def etaleAffineLocally (f : X ⟶ Y) : Prop :=
  ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
    CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigFlat g

/-- The universal affine étale chart condition holds exactly when every
commutative chart square has a rig-flat top arrow. -/
theorem etaleAffineLocally_iff (f : X ⟶ Y) :
    etaleAffineLocally f ↔
      ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
        [IsFormalAlgebraicSpace U] [IsAffine U]
        [IsFormalAlgebraicSpace V] [IsAffine V]
        {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
        CommSq g u v f → Etale u → Etale v →
          AffineFormalAlgebraicSpace.RigFlat g :=
  Iff.rfl

namespace etaleAffineLocally

/-- A rig-flat top arrow in every affine étale chart square establishes the
universal affine étale chart condition. -/
theorem of {f : X ⟶ Y}
    (h : ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace U] [IsAffine U]
      [IsFormalAlgebraicSpace V] [IsAffine V]
      {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
      CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigFlat g) :
    etaleAffineLocally f :=
  h

/-- The universal affine étale chart condition gives rig-flatness of the top
arrow of any specified affine étale chart square. -/
theorem spec {f : X ⟶ Y} (h : etaleAffineLocally f)
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V}
    (sq : CommSq g u v f) (hu : Etale u) (hv : Etale v) :
    AffineFormalAlgebraicSpace.RigFlat g :=
  h sq hu hv

end etaleAffineLocally

/-- The target admits an affine étale cover such that each fibre product with
the source admits an affine étale cover whose projections to the target chart
are rig-flat morphisms of affine formal algebraic spaces. -/
def existsCoverOnTarget (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
      (hY : IsEtaleAffineCover π),
    ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigFlatArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)

/-- The target-cover condition is equivalent to the existence of affine étale
covering families of the target and its fibre products with rig-flat projections
to each target chart. -/
theorem existsCoverOnTarget_iff (f : X ⟶ Y) :
    existsCoverOnTarget f ↔
      ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
          (hY : IsEtaleAffineCover π),
        ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
            (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
          ∀ k, isRigFlatArrow (hX.isFormal k) (hX.isAffine k)
              (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f) :=
  Iff.rfl

namespace existsCoverOnTarget

/-- An affine étale cover of the target and affine étale covers of its fibre
products with rig-flat projections establish the target-cover condition. -/
theorem of {f : X ⟶ Y} {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigFlatArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget f :=
  ⟨ι, Y_, π, hY, hX⟩

/-- The target-cover condition supplies an affine étale cover of the target
and affine étale covers of its fibre products with rig-flat projections. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
        (hY : IsEtaleAffineCover π),
      ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
        ∀ k, isRigFlatArrow (hX.isFormal k) (hX.isAffine k)
            (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f) :=
  h

end existsCoverOnTarget

/-- The source admits an affine étale cover whose charts factor through affine
formal algebraic spaces étale over the target by rig-flat morphisms. -/
def existsCoverOnSource (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
      (hX : IsEtaleAffineCover π),
    ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
        (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigFlatArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q

/-- The source-cover condition is equivalent to the existence of an affine
étale cover of the source with rig-flat factorizations through affine étale
charts of the target. -/
theorem existsCoverOnSource_iff (f : X ⟶ Y) :
    existsCoverOnSource f ↔
      ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
          (hX : IsEtaleAffineCover π),
        ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
            (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
            (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          Etale p ∧ π i ≫ f = q ≫ p ∧
            isRigFlatArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  Iff.rfl

namespace existsCoverOnSource

/-- An affine étale cover of the source with rig-flat factorizations through
affine étale target charts establishes the source-cover condition. -/
theorem of {f : X ⟶ Y} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
      (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigFlatArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q) :
    existsCoverOnSource f :=
  ⟨ι, X_, π, hX, hFac⟩

/-- The source-cover condition supplies an affine étale cover of the source
and compatible rig-flat factorizations through affine étale target charts. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnSource f) :
    ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
        (hX : IsEtaleAffineCover π),
      ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
          (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        Etale p ∧ π i ≫ f = q ≫ p ∧
          isRigFlatArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  h

end existsCoverOnSource

/-- For a morphism of locally Noetherian formal algebraic spaces, rig-flatness,
the universal affine étale chart condition, the target-cover condition, and the
source-cover condition are equivalent. -/
theorem tfae (f : X ⟶ Y) :
    List.TFAE [RigFlat f, etaleAffineLocally f, existsCoverOnTarget f,
      existsCoverOnSource f] :=
  sorry

/-- The existence of an affine étale cover of the target and affine étale
covers of its fibre products with rig-flat projections is equivalent to
rig-flatness of the morphism. -/
theorem iff_existsCoverOnTarget (f : X ⟶ Y) :
    existsCoverOnTarget f ↔ RigFlat f :=
  (tfae f).out 2 0

/-- The existence of an affine étale cover of the source with rig-flat
factorizations through affine étale target charts is equivalent to rig-flatness
of the morphism. -/
theorem iff_existsCoverOnSource (f : X ⟶ Y) :
    existsCoverOnSource f ↔ RigFlat f :=
  (tfae f).out 3 0

end RigFlat

end AlgebraicGeometry.FormalAlgebraicSpace
