/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap88.Definition_88_21_1_Formal
public import stacks_project.Chap88.Lemma_88_13_5

/-!
# Local tests of morphisms locally of finite type

A morphism of formal algebraic spaces is locally of finite type if and only if
this can be tested by a surjective étale square, by every étale vertical square,
or by Definition 87.11.1 coverings of the target or of the source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
variable (f : X ⟶ Y)

namespace LocallyOfFiniteType

/-- There is a commutative square of formal algebraic spaces over `f` whose
vertical arrows are étale (hence representable by algebraic spaces), `U ⟶ X`
is fppf-locally surjective, and `U ⟶ V` is locally of finite type. -/
def existsSurjectiveEtaleSquare : Prop :=
  ∃ (U V : (Over S)ᵒᵖ ⥤ Type u) (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y),
    IsFormalAlgebraicSpace U ∧ IsFormalAlgebraicSpace V ∧
      Etale pU ∧ Etale pV ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) pU ∧
          LocallyOfFiniteType q ∧ CommSq q pU pV f

namespace existsSurjectiveEtaleSquare

/-- A commutative square of formal algebraic spaces with étale vertical arrows,
fppf-locally surjective `U ⟶ X`, and locally-of-finite-type `U ⟶ V` witnesses
`existsSurjectiveEtaleSquare f`. -/
theorem of {U V : (Over S)ᵒᵖ ⥤ Type u} (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V]
    (hEtU : Etale pU) (hEtV : Etale pV)
    (hSurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) pU)
    (hFT : LocallyOfFiniteType q) (sq : CommSq q pU pV f) :
    existsSurjectiveEtaleSquare f :=
  sorry

/-- `existsSurjectiveEtaleSquare f` unpacks as a commutative square of formal
algebraic spaces with étale vertical arrows, fppf-locally surjective `U ⟶ X`,
and locally-of-finite-type `U ⟶ V`. -/
theorem iff : existsSurjectiveEtaleSquare f ↔
    ∃ (U V : (Over S)ᵒᵖ ⥤ Type u) (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y),
      IsFormalAlgebraicSpace U ∧ IsFormalAlgebraicSpace V ∧
        Etale pU ∧ Etale pV ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) pU ∧
            LocallyOfFiniteType q ∧ CommSq q pU pV f :=
  sorry

/-- `existsSurjectiveEtaleSquare f` supplies formal algebraic spaces `U`, `V`
and a commutative square with étale vertical arrows, fppf-locally surjective
`U ⟶ X`, and locally-of-finite-type `U ⟶ V`. -/
theorem spec (h : existsSurjectiveEtaleSquare f) :
    ∃ (U V : (Over S)ᵒᵖ ⥤ Type u) (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y),
      IsFormalAlgebraicSpace U ∧ IsFormalAlgebraicSpace V ∧
        Etale pU ∧ Etale pV ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) pU ∧
            LocallyOfFiniteType q ∧ CommSq q pU pV f :=
  sorry

end existsSurjectiveEtaleSquare

/-- For every commutative square of formal algebraic spaces over `f` whose
vertical arrows are étale (hence representable by algebraic spaces), the top
arrow `U ⟶ V` is locally of finite type. -/
def forallEtaleSquare : Prop :=
  ∀ {U V : (Over S)ᵒᵖ ⥤ Type u} (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
    Etale pU → Etale pV → CommSq q pU pV f → LocallyOfFiniteType q

namespace forallEtaleSquare

/-- A universal finite-type statement for top arrows of étale vertical squares
witnesses `forallEtaleSquare f`. -/
theorem of (h : ∀ {U V : (Over S)ᵒᵖ ⥤ Type u} (pU : U ⟶ X) (q : U ⟶ V)
    (pV : V ⟶ Y) [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
    Etale pU → Etale pV → CommSq q pU pV f → LocallyOfFiniteType q) :
    forallEtaleSquare f :=
  sorry

/-- `forallEtaleSquare f` means every commutative square of formal algebraic
spaces over `f` with étale vertical arrows has locally-of-finite-type top
arrow. -/
theorem iff : forallEtaleSquare f ↔
    ∀ (U V : (Over S)ᵒᵖ ⥤ Type u) (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
      Etale pU → Etale pV → CommSq q pU pV f → LocallyOfFiniteType q :=
  sorry

/-- `forallEtaleSquare f` implies that the top arrow of a commutative square of
formal algebraic spaces with étale vertical arrows is locally of finite type. -/
theorem spec (h : forallEtaleSquare f) {U V : (Over S)ᵒᵖ ⥤ Type u}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V]
    (hEtU : Etale pU) (hEtV : Etale pV) (sq : CommSq q pU pV f) :
    LocallyOfFiniteType q :=
  sorry

end forallEtaleSquare

/-- There is a Definition 87.11.1 covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits a Definition 87.11.1 covering
`{X_ ji ⟶ Y_ j ×_Y X}` with each `X_ ji ⟶ Y_ j` locally of finite type. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
      (_ : IsEtaleAffineCover π),
    ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f) (_ : IsEtaleAffineCover σ),
      ∀ k, LocallyOfFiniteType (σ k ≫ pullback.fst (π j) f)

namespace existsCoverOnTarget

/-- A Definition 87.11.1 covering of `Y`, together with Definition 87.11.1
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` are locally of
finite type, witnesses `existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f) (_ : IsEtaleAffineCover σ),
      ∀ k, LocallyOfFiniteType (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget f :=
  sorry

/-- `existsCoverOnTarget f` unpacks as a Definition 87.11.1 covering of `Y`
and, for each chart, a Definition 87.11.1 covering of the fibre product with
`X` whose projections to the chart are locally of finite type. -/
theorem iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
        (_ : IsEtaleAffineCover π),
      ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f) (_ : IsEtaleAffineCover σ),
        ∀ k, LocallyOfFiniteType (σ k ≫ pullback.fst (π j) f) :=
  sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 covering of `Y` and
compatible Definition 87.11.1 coverings of the fibre products with `X`. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y)
        (_ : IsEtaleAffineCover π),
      ∀ j, ∃ (ι' : Type u) (X_ : ι' → ((Over S)ᵒᵖ ⥤ Type u))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f) (_ : IsEtaleAffineCover σ),
        ∀ k, LocallyOfFiniteType (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- There is a Definition 87.11.1 covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space,
`Y_ i ⟶ Y` étale (hence representable by algebraic spaces), and
`X_ i ⟶ Y_ i` locally of finite type. -/
def existsCoverOnSource : Prop :=
  ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
      (_ : IsEtaleAffineCover π),
    ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
        (_ : IsFormalAlgebraicSpace Y_i) (_ : IsAffine Y_i)
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ LocallyOfFiniteType q ∧ π i ≫ f = q ≫ p

namespace existsCoverOnSource

/-- A Definition 87.11.1 covering of `X` with affine étale factorizations
through `Y` whose source legs are locally of finite type witnesses
`existsCoverOnSource f`. -/
theorem of {ι : Type u} {X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
      (_ : IsFormalAlgebraicSpace Y_i) (_ : IsAffine Y_i)
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      Etale p ∧ LocallyOfFiniteType q ∧ π i ≫ f = q ≫ p) :
    existsCoverOnSource f :=
  sorry

/-- `existsCoverOnSource f` unpacks as a Definition 87.11.1 covering of `X`
whose charts factor through affine formal algebraic spaces over `Y` by an
étale target leg and a locally-of-finite-type source leg. -/
theorem iff : existsCoverOnSource f ↔
    ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
        (_ : IsEtaleAffineCover π),
      ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
          (_ : IsFormalAlgebraicSpace Y_i) (_ : IsAffine Y_i)
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        Etale p ∧ LocallyOfFiniteType q ∧ π i ≫ f = q ≫ p :=
  sorry

/-- `existsCoverOnSource f` supplies a Definition 87.11.1 covering of `X` and
affine étale factorizations through `Y` with locally-of-finite-type source
legs. -/
theorem spec (h : existsCoverOnSource f) :
    ∃ (ι : Type u) (X_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ i, X_ i ⟶ X)
        (_ : IsEtaleAffineCover π),
      ∀ i, ∃ (Y_i : (Over S)ᵒᵖ ⥤ Type u)
          (_ : IsFormalAlgebraicSpace Y_i) (_ : IsAffine Y_i)
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        Etale p ∧ LocallyOfFiniteType q ∧ π i ≫ f = q ≫ p :=
  sorry

end existsCoverOnSource

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
