module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap87.Definition_87_11_1_Formal

/-!
# Local tests of representability by algebraic spaces

A morphism of formal algebraic spaces is representable by algebraic spaces
if and only if this can be tested by a surjective étale square, by every
square with representable vertical arrows, or by Definition 87.11.1
coverings of the target or of the source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- A family `{X_ i ⟶ X}` is a covering as in Definition 87.11.1 when each
source is an affine formal algebraic space, each map is étale (hence
representable by algebraic spaces), and the coproduct map is locally
surjective as a map of sheaves. -/
structure IsEtaleAffineCover {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) : Prop where
  /-- Each chart is an affine formal algebraic space. -/
  isAffine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i)
  /-- Each chart map is representable by algebraic spaces and étale. -/
  isEtale : ∀ i, etale (π i)
  /-- The coproduct of the chart maps is locally surjective. -/
  isCover : ∃ (c : Cofan X_) (hc : IsColimit c),
    Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)

namespace IsEtaleAffineCover

/-- Package a Definition 87.11.1 covering from affine étale charts whose
coproduct is locally surjective. -/
def of {ι : Type (max u v)} {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {π : ∀ i, X_ i ⟶ X}
    (hAffine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (hEtale : ∀ i, etale (π i))
    (hCover : ∃ (c : Cofan X_) (hc : IsColimit c),
      Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)) :
    IsEtaleAffineCover π where
  isAffine := hAffine
  isEtale := hEtale
  isCover := hCover

/-- A family is a Definition 87.11.1 covering iff its objects are affine
formal algebraic spaces, its maps are étale, and the coproduct is locally
surjective. -/
theorem iff {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} (π : ∀ i, X_ i ⟶ X) :
    IsEtaleAffineCover π ↔
      (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
        (∀ i, etale (π i)) ∧
          ∃ (c : Cofan X_) (hc : IsColimit c),
            Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) :=
  sorry

/-- A Definition 87.11.1 covering unpacks as affine sources, étale chart maps
(hence representable by algebraic spaces), and a locally surjective
coproduct. -/
theorem spec {ι : Type (max u v)}
    {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} {π : ∀ i, X_ i ⟶ X}
    (h : IsEtaleAffineCover π) :
    (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
      (∀ i, etale (π i)) ∧ (∀ i, representableByAlgebraicSpaces (π i)) ∧
        ∃ (c : Cofan X_) (hc : IsColimit c),
          Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) :=
  sorry

end IsEtaleAffineCover

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- `forallVerticalRepresentable f` means every commutative square of formal
algebraic spaces over `f` with representable vertical arrows has
representable top arrow. -/
theorem iff : forallVerticalRepresentable f ↔
    ∀ (U V : Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (pU : U ⟶ X) (q : U ⟶ V) (pV : V ⟶ Y)
      [IsFormalAlgebraicSpace U] [IsFormalAlgebraicSpace V],
      representableByAlgebraicSpaces pU → representableByAlgebraicSpaces pV →
        CommSq q pU pV f → representableByAlgebraicSpaces q :=
  sorry

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
  sorry

end forallVerticalRepresentable

/-- There is a Definition 87.11.1 covering `{Y_ j ⟶ Y}` such that each fibre
product `Y_ j ×_Y X` admits a Definition 87.11.1 covering
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

/-- A Definition 87.11.1 covering of `Y`, together with Definition 87.11.1
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
  sorry

/-- `existsCoverOnTarget f` unpacks as a Definition 87.11.1 covering of `Y`
and, for each chart, a Definition 87.11.1 covering of the fibre product with
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
  sorry

/-- `existsCoverOnTarget f` supplies a Definition 87.11.1 covering of `Y` and
compatible Definition 87.11.1 coverings of the fibre products with `X`. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type (max u v)) (Y_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j, ∃ (ι' : Type (max u v))
          (X_ : ι' → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (σ : ∀ k, X_ k ⟶ pullback (π j) f),
          IsEtaleAffineCover σ ∧
            ∀ k, representableByAlgebraicSpaces (σ k ≫ pullback.fst (π j) f) :=
  sorry

end existsCoverOnTarget

/-- There is a Definition 87.11.1 covering `{X_ i ⟶ X}` such that each chart
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

/-- A Definition 87.11.1 covering of `X` with affine factorizations through
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
  sorry

/-- `existsCoverOnSource f` unpacks as a Definition 87.11.1 covering of `X`
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
  sorry

/-- `existsCoverOnSource f` supplies a Definition 87.11.1 covering of `X` and
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
  sorry

end existsCoverOnSource

end representableByAlgebraicSpaces

end AlgebraicGeometry.ChosenBigFppfSite
