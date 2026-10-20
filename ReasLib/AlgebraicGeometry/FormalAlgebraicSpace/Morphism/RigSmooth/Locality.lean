module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleCover

/-!
# Affine étale locality of rig-smooth morphisms
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigSmooth

/-- Rig-smoothness of an arrow of affine formal algebraic spaces, with the formal
and affine hypotheses supplied explicitly. -/
def isRigSmoothArrow {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) : Prop :=
  @AffineFormalAlgebraicSpace.RigSmooth S U V hU hUaff hV hVaff g

/-- Rig-smoothness with explicit formal and affine hypotheses is equivalent to
the canonical affine rig-smoothness predicate. -/
theorem isRigSmoothArrow_iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) :
    isRigSmoothArrow hU hUaff hV hVaff g ↔
      @AffineFormalAlgebraicSpace.RigSmooth S U V hU hUaff hV hVaff g :=
  sorry

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Every commutative square over a morphism with affine formal sources and
étale vertical maps has a rig-smooth top arrow. -/
def etaleAffineLocally (f : X ⟶ Y) : Prop :=
  ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
    CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigSmooth g

/-- The universal affine étale chart condition holds exactly when all its
commutative chart squares have rig-smooth top arrows. -/
theorem etaleAffineLocally_iff (f : X ⟶ Y) :
    etaleAffineLocally f ↔
      ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
        [IsFormalAlgebraicSpace U] [IsAffine U]
        [IsFormalAlgebraicSpace V] [IsAffine V]
        {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
        CommSq g u v f → Etale u → Etale v →
          AffineFormalAlgebraicSpace.RigSmooth g :=
  sorry

namespace etaleAffineLocally

/-- A rig-smooth top arrow in every affine étale chart square establishes the
universal affine étale chart condition. -/
theorem of {f : X ⟶ Y}
    (h : ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace U] [IsAffine U]
      [IsFormalAlgebraicSpace V] [IsAffine V]
      {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
      CommSq g u v f → Etale u → Etale v →
        AffineFormalAlgebraicSpace.RigSmooth g) :
    etaleAffineLocally f :=
  sorry

/-- The universal affine étale chart condition gives rig-smoothness of the top
arrow of any specified affine étale chart square. -/
theorem spec {f : X ⟶ Y} (h : etaleAffineLocally f)
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V}
    (sq : CommSq g u v f) (hu : Etale u) (hv : Etale v) :
    AffineFormalAlgebraicSpace.RigSmooth g :=
  sorry

end etaleAffineLocally

/-- The target has an affine étale covering such that each pullback with the
source has an affine étale covering whose projections to the target chart
are rig-smooth. -/
def existsCoverOnTarget (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
      (hY : IsEtaleAffineCover π),
    ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigSmoothArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)

/-- The target covering condition is equivalent to the existence of affine
étale target charts and affine étale coverings of their pullbacks whose
projections to the target charts are rig-smooth. -/
theorem existsCoverOnTarget_iff (f : X ⟶ Y) :
    existsCoverOnTarget f ↔
      ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
          (hY : IsEtaleAffineCover π),
        ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
            (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
          ∀ k, isRigSmoothArrow (hX.isFormal k) (hX.isAffine k)
              (hY.isFormal j) (hY.isAffine j)
              (σ k ≫ pullback.fst (π j) f) :=
  sorry

namespace existsCoverOnTarget

/-- An affine étale covering of the target and affine étale coverings of its
pullbacks with rig-smooth projections establish the target covering condition. -/
theorem of {f : X ⟶ Y} {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigSmoothArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget f :=
  sorry

/-- The target covering condition supplies affine étale target charts and
affine étale coverings of their pullbacks with rig-smooth projections. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
        (hY : IsEtaleAffineCover π),
      ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
        ∀ k, isRigSmoothArrow (hX.isFormal k) (hX.isAffine k)
            (hY.isFormal j) (hY.isAffine j)
            (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- The source has an affine étale covering whose composites with the given
morphism factor through affine étale target charts by rig-smooth arrows. -/
def existsCoverOnSource (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
      (hX : IsEtaleAffineCover π),
    ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
        (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigSmoothArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q

/-- The source covering condition is equivalent to an affine étale source
covering whose composites factor through affine étale target charts by
rig-smooth arrows. -/
theorem existsCoverOnSource_iff (f : X ⟶ Y) :
    existsCoverOnSource f ↔
      ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
          (hX : IsEtaleAffineCover π),
        ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
            (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
            (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          Etale p ∧ π i ≫ f = q ≫ p ∧
            isRigSmoothArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  sorry

namespace existsCoverOnSource

/-- An affine étale source covering with rig-smooth factorizations through
affine étale target charts establishes the source covering condition. -/
theorem of {f : X ⟶ Y} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
      (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigSmoothArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q) :
    existsCoverOnSource f :=
  sorry

/-- The source covering condition supplies an affine étale source covering
and rig-smooth factorizations through affine étale target charts. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnSource f) :
    ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
        (hX : IsEtaleAffineCover π),
      ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
          (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        Etale p ∧ π i ≫ f = q ≫ p ∧
          isRigSmoothArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  sorry

end existsCoverOnSource

/-- For a morphism of locally Noetherian formal algebraic spaces, rig-smoothness,
the universal affine étale chart condition, the target covering condition, and
the source covering condition are equivalent. -/
theorem tfae (f : X ⟶ Y) :
    List.TFAE [RigSmooth f, etaleAffineLocally f, existsCoverOnTarget f,
      existsCoverOnSource f] :=
  sorry

/-- The existence of affine étale target charts with affine étale coverings of
their pullbacks having rig-smooth projections is equivalent to rig-smoothness. -/
theorem iff_existsCoverOnTarget (f : X ⟶ Y) :
    existsCoverOnTarget f ↔ RigSmooth f :=
  sorry

/-- The existence of an affine étale source covering with rig-smooth
factorizations through affine étale target charts is equivalent to rig-smoothness. -/
theorem iff_existsCoverOnSource (f : X ⟶ Y) :
    existsCoverOnSource f ↔ RigSmooth f :=
  sorry

end RigSmooth

end AlgebraicGeometry.FormalAlgebraicSpace
