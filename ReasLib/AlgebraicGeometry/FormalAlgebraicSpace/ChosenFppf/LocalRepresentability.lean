/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.EtaleCover
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Data.List.TFAE

/-!
# Local representability by algebraic spaces

Representability of a morphism between formal algebraic spaces can be tested
on surjective étale squares or affine étale covering families.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable (f : X ⟶ Y)

namespace representableByAlgebraicSpaces

/-- There is a commutative square of formal algebraic spaces over `f` whose
vertical arrows are representable by algebraic spaces, `U ⟶ X` is
surjective étale, and `U ⟶ V` is representable by algebraic spaces. -/
def existsSurjectiveEtaleSquare : Prop :=
  ∃ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y),
    IsFormalAlgebraicSpace U ∧ IsFormalAlgebraicSpace V ∧
      representableByAlgebraicSpaces pU ∧ representableByAlgebraicSpaces pV ∧
        etale pU ∧ Sheaf.IsLocallySurjective pU ∧
          representableByAlgebraicSpaces q ∧ CommSq q pU pV f

namespace existsSurjectiveEtaleSquare

/-- A commutative square of formal algebraic spaces with representable
vertical arrows, surjective étale `U ⟶ X`, and representable `U ⟶ V`
witnesses `existsSurjectiveEtaleSquare f`. -/
theorem of {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V]
    (hRepU : representableByAlgebraicSpaces pU)
    (hRepV : representableByAlgebraicSpaces pV) (hEt : etale pU)
    (hSurj : Sheaf.IsLocallySurjective pU)
    (hRepQ : representableByAlgebraicSpaces q) (sq : CommSq q pU pV f) :
    existsSurjectiveEtaleSquare f :=
  by
    exact ⟨U, V, pU, q, pV, inferInstance, inferInstance,
      hRepU, hRepV, hEt, hSurj, hRepQ, sq⟩

/-- `existsSurjectiveEtaleSquare f` unpacks as a commutative square of formal
algebraic spaces with representable vertical arrows, surjective étale
`U ⟶ X`, and representable `U ⟶ V`. -/
theorem iff : existsSurjectiveEtaleSquare f ↔
    ∃ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y),
      IsFormalAlgebraicSpace U ∧ IsFormalAlgebraicSpace V ∧
        representableByAlgebraicSpaces pU ∧ representableByAlgebraicSpaces pV ∧
          etale pU ∧ Sheaf.IsLocallySurjective pU ∧
            representableByAlgebraicSpaces q ∧ CommSq q pU pV f :=
  Iff.rfl

/-- `existsSurjectiveEtaleSquare f` supplies formal algebraic spaces `U`, `V`
and a commutative square with representable vertical arrows, surjective
étale `U ⟶ X`, and representable `U ⟶ V`. -/
theorem spec (h : existsSurjectiveEtaleSquare f) :
    ∃ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y),
      IsFormalAlgebraicSpace U ∧ IsFormalAlgebraicSpace V ∧
        representableByAlgebraicSpaces pU ∧ representableByAlgebraicSpaces pV ∧
          etale pU ∧ Sheaf.IsLocallySurjective pU ∧
            representableByAlgebraicSpaces q ∧ CommSq q pU pV f :=
  h

end existsSurjectiveEtaleSquare

/-- For every commutative square of formal algebraic spaces over `f` whose
vertical arrows are representable by algebraic spaces, the top arrow
`U ⟶ V` is representable by algebraic spaces. -/
def forallVerticalRepresentable : Prop :=
  ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
    representableByAlgebraicSpaces pU → representableByAlgebraicSpaces pV →
      CommSq q pU pV f → representableByAlgebraicSpaces q

namespace forallVerticalRepresentable

/-- A universal representability statement for top arrows of squares with
representable vertical arrows witnesses `forallVerticalRepresentable f`. -/
theorem of (h : ∀ {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
    representableByAlgebraicSpaces pU → representableByAlgebraicSpaces pV →
      CommSq q pU pV f → representableByAlgebraicSpaces q) :
    forallVerticalRepresentable f :=
  h

/-- `forallVerticalRepresentable f` means every commutative square of formal
algebraic spaces over `f` with representable vertical arrows has
representable top arrow. -/
theorem iff : forallVerticalRepresentable f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
      representableByAlgebraicSpaces pU → representableByAlgebraicSpaces pV →
        CommSq q pU pV f → representableByAlgebraicSpaces q :=
  by
    constructor
    · intro h U V pU q pV hU hV
      exact h pU q pV
    · intro h U V pU q pV hU hV
      exact h U V pU q pV

/-- `forallVerticalRepresentable f` implies that the top arrow of a
commutative square of formal algebraic spaces with representable vertical
arrows is representable by algebraic spaces. -/
theorem spec (h : forallVerticalRepresentable f)
    {U V : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
    [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V]
    (hRepU : representableByAlgebraicSpaces pU)
    (hRepV : representableByAlgebraicSpaces pV) (sq : CommSq q pU pV f) :
    representableByAlgebraicSpaces q :=
  h pU q pV hRepU hRepV sq

end forallVerticalRepresentable

/-- There is an affine étale covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits an affine étale covering
`{X_ ji ⟶ Y_ j ×_Y X}` with each `X_ ji ⟶ Y_ j` representable by algebraic
spaces. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ j, Y_ j ⟶ Y),
    IsEtaleAffineCover π ∧
      ∀ j, ∃ (ι' : Type (max u v))
        (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (σ : ∀ k, X_ k ⟶ pullback (π j) f),
        IsEtaleAffineCover σ ∧
          ∀ k, representableByAlgebraicSpaces (σ k ≫ pullback.fst (π j) f)

namespace existsCoverOnTarget

/-- An affine étale covering of `Y`, together with affine étale
coverings of each `Y_ j ×_Y X` whose projections to `Y_ j` are representable
by algebraic spaces, witnesses `existsCoverOnTarget f`. -/
theorem of {ι : Type (max u v)}
    {Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ j, Y_ j ⟶ Y) (hY : IsEtaleAffineCover π)
    (hX : ∀ j, ∃ (ι' : Type (max u v))
      (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (σ : ∀ k, X_ k ⟶ pullback (π j) f),
      IsEtaleAffineCover σ ∧
        ∀ k, representableByAlgebraicSpaces (σ k ≫ pullback.fst (π j) f)) :
    existsCoverOnTarget f :=
  ⟨ι, Y_, π, hY, hX⟩

/-- `existsCoverOnTarget f` unpacks as an affine étale covering of `Y`
and, for each chart, an affine étale covering of the fibre product with
`X` whose projections to the chart are representable by algebraic spaces. -/
theorem iff : existsCoverOnTarget f ↔
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          IsEtaleAffineCover σ ∧
            ∀ k, representableByAlgebraicSpaces (σ k ≫ pullback.fst (π j) f) :=
  Iff.rfl

/-- `existsCoverOnTarget f` supplies an affine étale covering of `Y` and
compatible affine étale coverings of the fibre products with `X`. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          IsEtaleAffineCover σ ∧
            ∀ k, representableByAlgebraicSpaces (σ k ≫ pullback.fst (π j) f) :=
  h

end existsCoverOnTarget

/-- There is an affine étale covering `{X_ i ⟶ X}` such that each chart
factors as `X_ i ⟶ Y_ i ⟶ Y` with `Y_ i` an affine formal algebraic space
and both legs representable by algebraic spaces. -/
def existsCoverOnSource : Prop :=
  ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X),
    IsEtaleAffineCover π ∧
      ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
        (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
        IsAffineFormalAlgebraicSpace Y_i ∧
          representableByAlgebraicSpaces p ∧ representableByAlgebraicSpaces q ∧
            π i ≫ f = q ≫ p

namespace existsCoverOnSource

/-- An affine étale covering of `X` with affine factorizations through
`Y` whose legs are representable by algebraic spaces witnesses
`existsCoverOnSource f`. -/
theorem of {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (hX : IsEtaleAffineCover π)
    (hFac : ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
      IsAffineFormalAlgebraicSpace Y_i ∧
        representableByAlgebraicSpaces p ∧ representableByAlgebraicSpaces q ∧
          π i ≫ f = q ≫ p) :
    existsCoverOnSource f :=
  ⟨ι, X_, π, hX, hFac⟩

/-- `existsCoverOnSource f` unpacks as an affine étale covering of `X`
whose charts factor through affine formal algebraic spaces over `Y` by
representable legs. -/
theorem iff : existsCoverOnSource f ↔
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            representableByAlgebraicSpaces p ∧
              representableByAlgebraicSpaces q ∧ π i ≫ f = q ≫ p :=
  Iff.rfl

/-- `existsCoverOnSource f` supplies an affine étale covering of `X` and
affine factorizations through `Y` with representable legs. -/
theorem spec (h : existsCoverOnSource f) :
    ∃ (ι : Type (max u v)) (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X),
      IsEtaleAffineCover π ∧
        ∀ i, ∃ (Y_i : Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (q : X_ i ⟶ Y_i) (p : Y_i ⟶ Y),
          IsAffineFormalAlgebraicSpace Y_i ∧
            representableByAlgebraicSpaces p ∧
              representableByAlgebraicSpaces q ∧ π i ≫ f = q ≫ p :=
  h

end existsCoverOnSource

/-- For a morphism between formal algebraic spaces, representability by
algebraic spaces is equivalent to the surjective étale square criterion,
the universal square criterion, and the affine étale covering criteria on
the target and on the source. -/
theorem tfae [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] :
    List.TFAE [representableByAlgebraicSpaces f, existsSurjectiveEtaleSquare f,
      forallVerticalRepresentable f, existsCoverOnTarget f,
      existsCoverOnSource f] :=
  sorry

/-- Representability by algebraic spaces is equivalent to the existence of a
commutative square of formal algebraic spaces with representable vertical
arrows, surjective étale `U ⟶ X`, and representable `U ⟶ V`. -/
theorem iff_existsSurjectiveEtaleSquare [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] :
    representableByAlgebraicSpaces f ↔ existsSurjectiveEtaleSquare f :=
  (tfae f).out 0 1

/-- Representability by algebraic spaces is equivalent to representability of
the top arrow of every commutative square of formal algebraic spaces with
representable vertical arrows. -/
theorem iff_forallVerticalRepresentable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] :
    representableByAlgebraicSpaces f ↔ forallVerticalRepresentable f :=
  (tfae f).out 0 2

/-- Representability by algebraic spaces is equivalent to the existence of an
affine étale covering of `Y` and then of each `Y_ j ×_Y X` whose
projections `X_ ji ⟶ Y_ j` are representable by algebraic spaces. -/
theorem iff_existsCoverOnTarget [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] :
    representableByAlgebraicSpaces f ↔ existsCoverOnTarget f :=
  (tfae f).out 0 3

/-- Representability by algebraic spaces is equivalent to the existence of an
affine étale covering of `X` factoring as `X_ i ⟶ Y_ i ⟶ Y` through
affine formal algebraic spaces with both legs representable by algebraic
spaces. -/
theorem iff_existsCoverOnSource [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] :
    representableByAlgebraicSpaces f ↔ existsCoverOnSource f :=
  (tfae f).out 0 4

end representableByAlgebraicSpaces

end AlgebraicGeometry.ChosenBigFppfSite
