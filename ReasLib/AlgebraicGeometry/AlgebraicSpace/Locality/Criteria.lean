/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtalePrecoverage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Locality criteria for morphism properties of algebraic spaces

The criteria are predicates on an arbitrary morphism property. Scheme-square
criteria use a scheme property and its existing lift `AlgebraicSpace.etaleLocal`.
The TFAE theorems keep arbitrary base change separate from étale locality:
étale locality alone does not imply stability under arbitrary base change.

The scheme-square comparison is Stacks, Tag 03MJ,
`tex/spaces-morphisms.tex:4085–4217`. The base-change and Zariski refinements
abstract the arguments of Tags 040Y and 03MM,
`tex/spaces-morphisms.tex:4398–4461,5834–5876`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty Limits

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Locality.Criteria

/-- Every scheme base change has `P`.
Stacks, Tags 040Y (3), 03MM (3), `tex/spaces-morphisms.tex:4405–4406,5841–5842`. -/
def forallScheme {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y), P (pullbackAlongScheme.snd f g)

/-- Every affine-scheme base change has `P`.
Stacks, Tags 040Y (4), 03MM (4), `tex/spaces-morphisms.tex:4407–4408,5843–5844`. -/
def forallAffine {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} (g : ofOver Z ⟶ Y),
    AlgebraicGeometry.IsAffine Z.left → P (pullbackAlongScheme.snd f g)

/-- The affine criterion expressed using every presentation of a pullback.
Stacks, Tag 03L3 (2), `tex/decent-spaces.tex:3952–3953`. -/
def forallAffineIsPullback {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → P pZ

/-- Every scheme-valued pullback has an apex satisfying the object property `Q`.
Stacks, Tag 03KZ, `tex/decent-spaces.tex:3673–3685`. -/
def forallSchemeObject {S : Scheme.{u}} (Q : AlgebraicSpace S → Prop) :
    MorphismProperty (AlgebraicSpace S) :=
  fun X Y f ↦ ∀ {Z : Over S} {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X}, IsPullback pZ pX g f → Q W

/-- Every affine-scheme-valued pullback has an apex satisfying `Q`.
Stacks, Tag 03L3 (3), `tex/decent-spaces.tex:3954–3955`. -/
def forallAffineObject {S : Scheme.{u}} (Q : AlgebraicSpace S → Prop)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Q W

/-- Every étale pullback from an affine scheme has apex satisfying `Q`.
This only tests target charts, and imposes no source-locality condition.
Stacks, Tag 03WG (3), `tex/spaces-morphisms.tex:3699–3700`. -/
def forallAffineEtaleObject {S : Scheme.{u}} (Q : AlgebraicSpace S → Prop)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ {V : Over S} [AlgebraicGeometry.IsAffine V.left] {W : AlgebraicSpace S}
    {g : ofOver V ⟶ Y} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
    Etale g → IsPullback pV pX g f → Q W

/-- A single Zariski covering of the target has `P` on every inverse-image
projection. Unlike `existsZariskiCover`, this imposes no source covering.
Stacks, Tag 03L3 (4), `tex/decent-spaces.tex:3956–3957`. -/
def existsZariskiCoverOnTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, v} Y),
    ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → P pYi

/-- Some surjective étale scheme atlas of the target gives a base change with `P`.
Stacks, Tags 040Y (5), 03MM (5), `tex/spaces-morphisms.tex:4409–4410,5845–5846`. -/
def existsSurjectiveEtaleTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y),
    (over (@AlgebraicGeometry.Etale)).presheaf b ∧
      Surjective b ∧ P (pullbackAlongScheme.snd f b)

/-- Some surjective étale scheme atlas of the source gives a composite with `P`.
Stacks, Tags 040Y (6), 03MM (6), `tex/spaces-morphisms.tex:4411–4413,5847–5849`. -/
def existsSurjectiveEtaleSource {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X),
    (over (@AlgebraicGeometry.Etale)).presheaf φ ∧ Surjective φ ∧ P (φ ≫ f)

/-- The universal étale scheme-square criterion is the existing canonical lift.
Stacks, Tag 03MJ (1), `tex/spaces-morphisms.tex:4097–4116`. -/
abbrev forallEtaleSquare {S : Scheme.{u}} (Q : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  etaleLocal Q f

/-- Some étale scheme square has surjective source leg and top arrow with `Q`.
Surjectivity of the target leg is not required.
Stacks, Tag 03MJ (2), `tex/spaces-morphisms.tex:4097–4118`. -/
def existsEtaleSquare {S : Scheme.{u}} (Q : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧ Surjective a ∧ Q h.left

/-- Zariski coverings of the target and its full inverse images have pieces with `P`.
The range equality specifies the entire inverse image, including empty ones.
Stacks, Tags 040Y (9), 03MM (9), `tex/spaces-morphisms.tex:4432–4434,5868–5870`. -/
def existsZariskiCover {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ 𝒱 : ZariskiCover.{u, v} Y, ∀ i : 𝒱.I₀,
    ∃ (Xi : AlgebraicSpace S) (ι : Xi ⟶ X) (_ : IsOpenImmersion ι)
      (𝒰 : ZariskiCover.{u, v} Xi) (h : ∀ j, 𝒰.X j ⟶ 𝒱.X i),
      (∀ j, 𝒰.f j ≫ ι ≫ f = h j ≫ 𝒱.f i) ∧
        (∀ j, P (h j)) ∧
          Set.range (Points.map ι) =
            (Points.map f) ⁻¹' Set.range (Points.map (𝒱.f i))

/-- Some target cover for `K` has base-change projections with `P`.
Stacks, Tag 0CG1 (e), `additional-sources-1.md:194072–194073`, for smooth `K`;
the predicate itself makes sense for any precoverage. -/
def existsCoverOnTarget {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    (K : Precoverage (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ 𝒰 : K.ZeroHypercover.{u} Y, ∀ i : 𝒰.I₀, P (pullback.snd f (𝒰.f i))

/-- Some source cover for `K` has composites with `P`.
Stacks, Tag 0CG1 (f), `additional-sources-1.md:194074–194075`, for étale `K`;
the predicate itself makes sense for any precoverage. -/
def existsCoverOnSource {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    (K : Precoverage (AlgebraicSpace S)) {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop :=
  ∃ 𝒰 : K.ZeroHypercover.{u} X, ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f)

/-- A surjective étale scheme atlas of the target has `P` on every pullback
projection. This is the presentation-independent version of
`existsSurjectiveEtaleTarget`.
Stacks, Tag 03MM (5), `tex/spaces-morphisms.tex:5845–5846`. -/
def existsEtaleOnTarget {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∃ (V : Over S) (b : ofOver V ⟶ Y), Etale b ∧ Surjective b ∧
    ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX b f → P pV

/-- The chosen and arbitrary pullback formulations agree for an
isomorphism-invariant property.
Stacks, Tags 040Y (3), 03MM (3), `tex/spaces-morphisms.tex:4405–4406,5841–5842`. -/
theorem forallScheme_iff_isPullback {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    forallScheme P f ↔
      ∀ {Z : Over S} {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
        {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
        IsPullback pZ pX g f → P pZ :=
  sorry

/-- Chosen and arbitrary affine pullbacks agree for an isomorphism-invariant
property. No source or target locality is needed for this comparison. -/
theorem forallAffine_iff_isPullback {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S)) [P.RespectsIso]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    forallAffine P f ↔ forallAffineIsPullback P f := by
  constructor
  · intro h Z hZ W g pZ pX sq
    let e := sq.isoIsPullback _ _ (pullbackAlongScheme.isPullback f g).flip
    have he : e.hom ≫ pullbackAlongScheme.snd f g = pZ :=
      sq.isoIsPullback_hom_fst _ _ (pullbackAlongScheme.isPullback f g).flip
    rw [← he]
    exact (P.cancel_left_of_respectsIso _ _).mpr (h g hZ)
  · intro h Z g hZ
    letI := hZ
    exact h (pullbackAlongScheme.isPullback f g).flip

/-- The locality argument for relative object properties uses only Zariski
locality of objects and preservation under representable morphisms. In
particular it does not assume étale locality at the source.
Stacks, Tags 03KE, 03KF and 03L3 (1)–(4),
`tex/decent-spaces.tex:828–906,909–920,3945–3980`. -/
theorem relativeObject_tfae {S : Scheme.{u}} (Q : AlgebraicSpace S → Prop)
    (hlocal : ∀ (W : AlgebraicSpace S) (𝒰 : ZariskiCover.{u, u} W),
      (∀ i, Q (𝒰.X i)) → Q W)
    (hrepresentable : ∀ {W V : AlgebraicSpace S} (g : W ⟶ V),
      yoneda.relativelyRepresentable g → Q V → Q W)
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ forallSchemeObject Q f
      , forallAffineIsPullback (forallSchemeObject Q) f
      , forallAffineObject Q f
      , existsZariskiCoverOnTarget.{u, u} (forallSchemeObject Q) f ] :=
  sorry

/-- A target-local property can be tested on a surjective étale scheme atlas.
Source locality is not needed.
Stacks, Tag 03L3 (5), `tex/decent-spaces.tex:3959–3964,3983–4010`. -/
theorem iff_existsEtaleOnTarget {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtTarget (@etalePrecoverage S)] [P.IsStableUnderBaseChange]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    P f ↔ existsEtaleOnTarget P f :=
  sorry

/-- Target locality and arbitrary base-change stability give scheme, affine,
étale-atlas and single target-Zariski-cover tests. No source locality is assumed;
in particular this applies to affine morphisms.
Stacks, Tag 03WG (2), (4), (5), `tex/spaces-morphisms.tex:3698–3704,3728–3730`,
and Tags 040Y (3), (4), 03MM (3), (4). -/
theorem targetLocal_tfae {S : Scheme.{u}}
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtTarget (@etalePrecoverage S)] [P.IsStableUnderBaseChange]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ P f, forallScheme P f, forallAffine P f
      , existsEtaleOnTarget P f, existsZariskiCoverOnTarget.{u, v} P f ] :=
  sorry

/-- Étale locality on the source and target, together with arbitrary base-change
stability, gives the base-change, atlas, cover, and Zariski criteria.
Stacks, Tags 040Y and 03MM, `tex/spaces-morphisms.tex:4398–4461,5834–5876`;
the covering argument is Tag 0CG1 (e),(f),
`additional-sources-1.md:194072–194075`, restricted to étale coverings. -/
theorem tfae {S : Scheme.{u}} (P : MorphismProperty (AlgebraicSpace S))
    [P.IsLocalAtSource (@etalePrecoverage S)]
    [P.IsLocalAtTarget (@etalePrecoverage S)] [P.IsStableUnderBaseChange]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ P f, forallScheme P f, forallAffine P f
      , existsSurjectiveEtaleTarget P f, existsSurjectiveEtaleSource P f
      , existsZariskiCover.{u, v} P f, existsEtaleOnTarget P f
      , existsCoverOnTarget P (@etalePrecoverage S) f
      , existsCoverOnSource P (@etalePrecoverage S) f ] :=
  sorry

/-- The lift of an étale-local scheme property has the eight generic criteria.
Arbitrary base-change stability is required only for the arbitrary scheme and
affine base-change tests. There is no smooth locality hypothesis.
Stacks, Tag 03MJ and Remark 67.22.4,
`tex/spaces-morphisms.tex:4097–4118,4213–4218`, and the generic argument of
Tags 040Y, 03MM, `tex/spaces-morphisms.tex:4398–4461,5834–5876`. -/
theorem etaleLocal_tfae {S : Scheme.{u}} (Q : MorphismProperty Scheme.{u})
    [IsEtaleLocalAtSourceAndTarget Q] [Q.IsStableUnderBaseChange]
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE
      [ etaleLocal Q f
      , forallScheme (etaleLocal Q) f
      , forallAffine (etaleLocal Q) f
      , existsSurjectiveEtaleTarget (etaleLocal Q) f
      , existsSurjectiveEtaleSource (etaleLocal Q) f
      , forallEtaleSquare Q f
      , existsEtaleSquare Q f
      , existsZariskiCover.{u, v} (etaleLocal Q) f ] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Locality.Criteria
