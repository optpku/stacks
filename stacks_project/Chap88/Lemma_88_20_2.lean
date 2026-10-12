/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1
public import stacks_project.Chap88.Lemma_88_13_5

/-!
# Local tests of rig-étaleness for locally Noetherian formal algebraic spaces

Lemma 88.20.2 records that a morphism of locally Noetherian formal algebraic
spaces is rig-étale if and only if affine étale charts, a Definition 87.11.1
cover of the target, or a Definition 87.11.1 cover of the source detect
rig-étaleness of the corresponding arrows of `WAdm^Noeth`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace RigEtale

/-- Apply `AffineFormalAlgebraicSpace.RigEtale` with affine and formal
hypotheses supplied explicitly, typically from an `IsEtaleAffineCover`. -/
def isRigEtaleArrow {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) : Prop :=
  @AffineFormalAlgebraicSpace.RigEtale S U V hU hUaff hV hVaff g

/-- `isRigEtaleArrow` is `AffineFormalAlgebraicSpace.RigEtale` with explicit
affine and formal hypotheses. -/
theorem isRigEtaleArrow_iff {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    (hU : IsFormalAlgebraicSpace U) (hUaff : IsAffine U)
    (hV : IsFormalAlgebraicSpace V) (hVaff : IsAffine V)
    (g : U ⟶ V) :
    isRigEtaleArrow hU hUaff hV hVaff g ↔
      @AffineFormalAlgebraicSpace.RigEtale S U V hU hUaff hV hVaff g :=
  sorry

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Every commutative square of `f` against étale maps from affine formal
algebraic spaces has top arrow corresponding to a rig-étale map in
`WAdm^Noeth`. This is condition (2) of the TFAE. -/
def etaleAffineLocally (f : X ⟶ Y) : Prop :=
  ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
    CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigEtale g

/-- `etaleAffineLocally f` means every étale affine-chart square over `f` has
top arrow a rig-étale morphism of affine formal algebraic spaces. -/
theorem etaleAffineLocally_iff (f : X ⟶ Y) :
    etaleAffineLocally f ↔
      ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
        [IsFormalAlgebraicSpace U] [IsAffine U]
        [IsFormalAlgebraicSpace V] [IsAffine V]
        {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
        CommSq g u v f → Etale u → Etale v →
          AffineFormalAlgebraicSpace.RigEtale g :=
  sorry

namespace etaleAffineLocally

/-- A universal étale affine-chart correspondence witnesses
`etaleAffineLocally f`. -/
theorem of {f : X ⟶ Y}
    (h : ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace U] [IsAffine U]
      [IsFormalAlgebraicSpace V] [IsAffine V]
      {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
      CommSq g u v f → Etale u → Etale v →
        AffineFormalAlgebraicSpace.RigEtale g) :
    etaleAffineLocally f :=
  sorry

/-- `etaleAffineLocally f` tests rig-étaleness on the top arrow of every
étale affine chart square over `f`. -/
theorem spec {f : X ⟶ Y} (h : etaleAffineLocally f)
    {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V}
    (sq : CommSq g u v f) (hu : Etale u) (hv : Etale v) :
    AffineFormalAlgebraicSpace.RigEtale g :=
  sorry

end etaleAffineLocally

/-- There is a Definition 87.11.1 covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits a Definition 87.11.1 covering
`{X_ ji ⟶ Y_ j ×_Y X}` with each `X_ ji ⟶ Y_ j` corresponding to a
rig-étale map in `WAdm^Noeth`. This is condition (3) of the TFAE. -/
def existsCoverOnTarget (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
      (hY : IsEtaleAffineCover π),
    ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)

/-- `existsCoverOnTarget f` unpacks as a Definition 87.11.1 covering of `Y`
and, for each chart, a Definition 87.11.1 covering of the fibre product with
`X` whose projections to the chart are rig-étale morphisms of affine formal
algebraic spaces. -/
theorem existsCoverOnTarget_iff (f : X ⟶ Y) :
    existsCoverOnTarget f ↔
      ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
          (hY : IsEtaleAffineCover π),
        ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
            (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
          ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
              (hY.isFormal j) (hY.isAffine j)
              (σ k ≫ pullback.fst (π j) f) :=
  sorry

namespace existsCoverOnTarget

/-- A Definition 87.11.1 covering of `Y`, together with Definition 87.11.1
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` are rig-étale,
witnesses `existsCoverOnTarget f`. -/
theorem of {f : X ⟶ Y} {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
      ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
          (hY.isFormal j) (hY.isAffine j) (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget f :=
  sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 covering of `Y` and
compatible Definition 87.11.1 coverings of the fibre products with `X`. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
        (hY : IsEtaleAffineCover π),
      ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f) (hX : IsEtaleAffineCover σ),
        ∀ k, isRigEtaleArrow (hX.isFormal k) (hX.isAffine k)
            (hY.isFormal j) (hY.isAffine j)
            (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- There is a Definition 87.11.1 covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space,
`Y_ i ⟶ Y` étale (hence representable by algebraic spaces), and
`X_ i ⟶ Y_ i` corresponding to a rig-étale map in `WAdm^Noeth`. This is
condition (4) of the TFAE. -/
def existsCoverOnSource (f : X ⟶ Y) : Prop :=
  ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
      (hX : IsEtaleAffineCover π),
    ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
        (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q

/-- `existsCoverOnSource f` unpacks as a Definition 87.11.1 covering of `X`
whose charts factor through affine étale charts of `Y` by rig-étale morphisms
of affine formal algebraic spaces. -/
theorem existsCoverOnSource_iff (f : X ⟶ Y) :
    existsCoverOnSource f ↔
      ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
          (hX : IsEtaleAffineCover π),
        ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
            (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
            (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          Etale p ∧ π i ≫ f = q ≫ p ∧
            isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  sorry

namespace existsCoverOnSource

/-- A Definition 87.11.1 covering of `X` with affine étale factorizations
through `Y` corresponding to rig-étale maps in `WAdm^Noeth` witnesses
`existsCoverOnSource f`. -/
theorem of {f : X ⟶ Y} {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
      (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ π i ≫ f = q ≫ p ∧
        isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q) :
    existsCoverOnSource f :=
  sorry

/-- `existsCoverOnSource f` supplies a Definition 87.11.1 covering of `X` and
affine étale factorizations through `Y`. -/
theorem spec {f : X ⟶ Y} (h : existsCoverOnSource f) :
    ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
        (hX : IsEtaleAffineCover π),
      ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
          (hYF : IsFormalAlgebraicSpace Y_i) (hYA : IsAffine Y_i)
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        Etale p ∧ π i ≫ f = q ≫ p ∧
          isRigEtaleArrow (hX.isFormal i) (hX.isAffine i) hYF hYA q :=
  sorry

end existsCoverOnSource

/-- Lemma 88.20.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally Noetherian formal algebraic spaces over `S`. The following are
equivalent: `RigEtale f`, that `f` is rig-étale; `etaleAffineLocally f`,
that every étale affine-chart square over `f` has top arrow corresponding to
a rig-étale map in `WAdm^Noeth`; `existsCoverOnTarget f`, that some covering
`{Y_ j ⟶ Y}` as in Definition 87.11.1 has, for each `j`, a covering
`{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 whose maps `X_ ji ⟶ Y_ j`
correspond to rig-étale maps in `WAdm^Noeth`; and `existsCoverOnSource f`,
that some covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as
`X_ i ⟶ Y_ i ⟶ Y` with each `Y_ i` an affine formal algebraic space, each
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and each
`X_ i ⟶ Y_ i` corresponding to a rig-étale map in `WAdm^Noeth`. -/
@[stacks 0GCZ]
theorem tfae (f : X ⟶ Y) :
    List.TFAE [RigEtale f, etaleAffineLocally f, existsCoverOnTarget f,
      existsCoverOnSource f] :=
  sorry

/-- Condition (2) of the TFAE is equivalent to condition (1): testing
rig-étaleness on every étale affine-chart square is equivalent to
`RigEtale f`. -/
theorem etaleAffineLocally_iff_rigEtale (f : X ⟶ Y) :
    etaleAffineLocally f ↔ RigEtale f :=
  sorry

/-- Condition (3) of the TFAE is equivalent to condition (1): a
Definition 87.11.1 covering of the target and then of each fibre product
witnesses rig-étaleness iff `f` is rig-étale. -/
theorem iff_existsCoverOnTarget (f : X ⟶ Y) :
    existsCoverOnTarget f ↔ RigEtale f :=
  sorry

/-- Condition (4) of the TFAE is equivalent to condition (1): a
Definition 87.11.1 covering of the source factoring through affine étale
charts of the target witnesses rig-étaleness iff `f` is rig-étale. -/
theorem iff_existsCoverOnSource (f : X ⟶ Y) :
    existsCoverOnSource f ↔ RigEtale f :=
  sorry

end RigEtale

end AlgebraicGeometry.FormalAlgebraicSpace
