module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleCover

/-!
# Local tests of rig-étaleness for locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigEtale

/-- Rig-étaleness of an affine formal morphism with its formal and affine
hypotheses supplied explicitly. -/
def isRigEtaleArrow {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) : Prop :=
  @AffineFormalAlgebraicSpace.RigEtale S U V hU hUaff hV hVaff g

/-- Rig-étaleness with explicit formal and affine hypotheses agrees with
the canonical affine formal morphism predicate. -/
theorem isRigEtaleArrow_iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) :
    isRigEtaleArrow hU hUaff hV hVaff g ↔
      @AffineFormalAlgebraicSpace.RigEtale S U V hU hUaff hV hVaff g :=
  Iff.rfl

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Every commutative square over a morphism with affine formal charts and
étale vertical maps has a rig-étale horizontal arrow. -/
def etaleAffineLocally (f : X ⟶ Y) : Prop :=
  ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
    CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigEtale g

/-- The universal affine étale chart predicate is equivalent to
rig-étaleness of the horizontal arrow in every such square. -/
theorem etaleAffineLocally_iff (f : X ⟶ Y) :
    etaleAffineLocally f ↔
      ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
        [IsFormalAlgebraicSpace U] [IsAffine U]
        [IsFormalAlgebraicSpace V] [IsAffine V]
        {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
        CommSq g u v f → Etale u → Etale v →
          AffineFormalAlgebraicSpace.RigEtale g :=
  Iff.rfl

namespace etaleAffineLocally

/-- A universal rig-étale affine étale chart test establishes the
corresponding chart predicate. -/
theorem of {f : X ⟶ Y}
    (h : ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace U] [IsAffine U]
      [IsFormalAlgebraicSpace V] [IsAffine V]
      {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
      CommSq g u v f → Etale u → Etale v →
        AffineFormalAlgebraicSpace.RigEtale g) :
    etaleAffineLocally f :=
  h

/-- The universal affine étale chart predicate gives rig-étaleness of
the horizontal arrow in any specified chart square. -/
theorem spec {f : X ⟶ Y} (h : etaleAffineLocally f)
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V}
    (sq : CommSq g u v f) (hu : Etale u) (hv : Etale v) :
    AffineFormalAlgebraicSpace.RigEtale g :=
  h sq hu hv

end etaleAffineLocally

/-- There is an affine étale covering of the target such that each
fibre product with the source has an affine étale covering whose projections
to the target chart are rig-étale. -/
def existsCoverOnTarget (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
      (hY : IsEtaleAffineCover π),
    ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)

/-- The target-cover predicate is equivalent to the existence of affine
étale target charts and affine étale coverings of their fibre products whose
projections to the target charts are rig-étale. -/
theorem existsCoverOnTarget_iff (f : X ⟶ Y) :
    existsCoverOnTarget f ↔
      ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
          (hY : IsEtaleAffineCover π),
        ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
            (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
          ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
              (hY.isFormal j) (hY.isAffine j)
              (σ k ≫ pullback.fst (π j) f) :=
  Iff.rfl

namespace existsCoverOnTarget

/-- An affine étale target covering with affine étale coverings of its
fibre products and rig-étale projections establishes the target-cover predicate. -/
theorem of {f : X ⟶ Y} {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget f :=
  ⟨ι, Y_, π, hY, hX⟩

/-- The target-cover predicate supplies affine étale target charts and
coverings of their fibre products with rig-étale projections. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
        (hY : IsEtaleAffineCover π),
      ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
        ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
            (hY.isFormal j) (hY.isAffine j)
            (σ k ≫ pullback.fst (π j) f) :=
  h

end existsCoverOnTarget

/-- There is an affine étale covering of the source whose chart maps
factor through affine étale target charts by rig-étale morphisms. -/
def existsCoverOnSource (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
      (hX : IsEtaleAffineCover π),
    ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
        (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q

/-- The source-cover predicate is equivalent to the existence of an
affine étale source covering and rig-étale factorizations through affine
étale target charts. -/
theorem existsCoverOnSource_iff (f : X ⟶ Y) :
    existsCoverOnSource f ↔
      ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
          (hX : IsEtaleAffineCover π),
        ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
            (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
            (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          Etale p ∧ π i ≫ f = q ≫ p ∧
            isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  Iff.rfl

namespace existsCoverOnSource

/-- An affine étale source covering with rig-étale factorizations
through affine étale target charts establishes the source-cover predicate. -/
theorem of {f : X ⟶ Y} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
      (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q) :
    existsCoverOnSource f :=
  ⟨ι, X_, π, hX, hFac⟩

/-- The source-cover predicate supplies an affine étale source covering
and rig-étale factorizations through affine étale target charts. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnSource f) :
    ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
        (hX : IsEtaleAffineCover π),
      ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
          (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        Etale p ∧ π i ≫ f = q ≫ p ∧
          isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  h

end existsCoverOnSource

/-- For a morphism of locally Noetherian formal algebraic spaces,
rig-étaleness, the universal affine étale chart test, the target-cover
condition, and the source-cover condition are equivalent. -/
theorem tfae (f : X ⟶ Y) :
    List.TFAE [RigEtale f, etaleAffineLocally f, existsCoverOnTarget f,
      existsCoverOnSource f] :=
  sorry

/-- An affine étale target covering with rig-étale projections from
coverings of its fibre products exists if and only if the morphism is rig-étale. -/
theorem iff_existsCoverOnTarget (f : X ⟶ Y) :
    existsCoverOnTarget f ↔ RigEtale f :=
  (tfae f).out 2 0

/-- An affine étale source covering with rig-étale factorizations through
affine étale target charts exists if and only if the morphism is rig-étale. -/
theorem iff_existsCoverOnSource (f : X ⟶ Y) :
    existsCoverOnSource f ↔ RigEtale f :=
  (tfae f).out 3 0

end RigEtale

end AlgebraicGeometry.FormalAlgebraicSpace
