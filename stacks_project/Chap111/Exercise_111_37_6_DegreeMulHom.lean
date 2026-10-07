module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic

/-!
# Degree-multiplying ring maps and the induced morphisms of `Proj`

A ring homomorphism that multiplies degrees by a fixed integer `e ≥ 1` is not a
`GradedRingHom` unless `e = 1`. This leaf records that morphism type together with
the open domain and glued scheme morphism it induces on projective spectra.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  {e : ℕ}

/-- A ring homomorphism between `ℕ`-graded rings which multiplies degrees by a fixed
integer `e ≥ 1`. -/
structure DegreeMulHom (𝒜 : ℕ → σ) (ℬ : ℕ → τ) (e : ℕ) extends A →+* B where
  /-- The degree multiplier is at least one. -/
  one_le_degree : 1 ≤ e
  /-- Homogeneous elements of degree `d` are sent into degree `d * e`. -/
  map_mem : ∀ {d : ℕ} {x : A}, x ∈ 𝒜 d → toRingHom x ∈ ℬ (d * e)

namespace DegreeMulHom

/-- Package a ring homomorphism that multiplies degrees by `e` as a `DegreeMulHom`. -/
def ofRingHom {e : ℕ} (f : A →+* B) (he : 1 ≤ e)
    (hmem : ∀ {d : ℕ} {x : A}, x ∈ 𝒜 d → f x ∈ ℬ (d * e)) :
    DegreeMulHom 𝒜 ℬ e where
  toRingHom := f
  one_le_degree := he
  map_mem := hmem

/-- The underlying ring homomorphism of `ofRingHom` is the given map. -/
theorem ofRingHom_toRingHom {e : ℕ} (f : A →+* B) (he : 1 ≤ e)
    (hmem : ∀ {d : ℕ} {x : A}, x ∈ 𝒜 d → f x ∈ ℬ (d * e)) :
    (ofRingHom f he hmem).toRingHom = f := sorry

/-- A `DegreeMulHom` is determined by its underlying ring homomorphism. -/
theorem toRingHom_injective {e : ℕ} :
    Function.Injective (toRingHom : DegreeMulHom 𝒜 ℬ e → A →+* B) := sorry

/-- Homogeneous elements of degree `d` land in degree `d * e`. -/
theorem map_mem_spec (ψ : DegreeMulHom 𝒜 ℬ e) {d : ℕ} {x : A}
    (hx : x ∈ 𝒜 d) : ψ.toRingHom x ∈ ℬ (d * e) := sorry

/-- The image of a power of `f` is a power of the image of `f`. -/
theorem toRingHom_mem_powers (ψ : DegreeMulHom 𝒜 ℬ e) {f : A} {x : A}
    (hx : x ∈ Submonoid.powers f) :
    ψ.toRingHom x ∈ Submonoid.powers (ψ.toRingHom f) := sorry

/-- Multiplying the source degree by `e` recovers the target degree of an `n`-fold multiple. -/
theorem map_mem_nsmul (ψ : DegreeMulHom 𝒜 ℬ e) {d n : ℕ} {x : A}
    (hx : x ∈ 𝒜 (n • d)) : ψ.toRingHom x ∈ ℬ (n • (d * e)) := sorry

/-- When `e = 1`, membership in degree `d * 1` is membership in degree `d`. -/
theorem map_mem_degree_one (ψ : DegreeMulHom 𝒜 ℬ 1) {d : ℕ} {x : A}
    (hx : x ∈ 𝒜 d) : ψ.toRingHom x ∈ ℬ d := sorry

/-- The `e = 1` case is an ordinary homomorphism of graded rings. -/
def toGradedRingHom (ψ : DegreeMulHom 𝒜 ℬ 1) : 𝒜 →+*ᵍ ℬ where
  toRingHom := ψ.toRingHom
  map_mem := map_mem_degree_one ψ

end DegreeMulHom

namespace PositiveHomogeneous

/-- Transport a positive homogeneous element along a degree-multiplying ring map. -/
def degreeMulMap (ψ : DegreeMulHom 𝒜 ℬ e) (f : PositiveHomogeneous 𝒜) :
    PositiveHomogeneous ℬ where
  val := ψ.toRingHom f.val
  degree := f.degree * e
  degree_pos := Nat.mul_pos f.degree_pos (Nat.succ_le_iff.mp ψ.one_le_degree)
  mem_degree := ψ.map_mem f.mem_degree

end PositiveHomogeneous

namespace DegreeMulHom

/-- The open `U = ⋃_{f ∈ R₊ homogeneous} D₊(ψ(f)) ⊆ Proj ℬ` on which `ψ` induces a
morphism of projective spectra. -/
abbrev domain (ψ : DegreeMulHom 𝒜 ℬ e) : (Proj ℬ).Opens :=
  iSup fun f : PositiveHomogeneous 𝒜 ↦ Proj.basicOpen ℬ (ψ.toRingHom f.val)

/-- A positive homogeneous basic open is contained in the induced domain. -/
theorem basicOpen_le_domain (ψ : DegreeMulHom 𝒜 ℬ e)
    {f : A} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    Proj.basicOpen ℬ (ψ.toRingHom f) ≤ domain ψ := sorry

/-- A point of `Proj ℬ` lies in the induced domain if and only if some positive-degree
homogeneous element of `𝒜` is sent outside the corresponding homogeneous ideal. -/
theorem mem_domain_iff (ψ : DegreeMulHom 𝒜 ℬ e) (p : Proj ℬ) :
    p ∈ domain ψ ↔
      ∃ f : A, ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d ∧ ψ.toRingHom f ∉ p.asHomogeneousIdeal := sorry

/-- Membership in the induced domain is equivalent to the irrelevant ideal of `𝒜` not
being contained in the comap of the point. -/
theorem mem_domain_iff_not_irrelevant_le (ψ : DegreeMulHom 𝒜 ℬ e) (p : Proj ℬ) :
    p ∈ domain ψ ↔
      ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
          p.asHomogeneousIdeal.toIdeal.comap ψ.toRingHom := sorry

/-- The corresponding point of `Proj 𝒜` associated to a point of the induced domain,
with homogeneous ideal `Ideal.comap ψ.toRingHom` of the original point. -/
def comapFun (ψ : DegreeMulHom 𝒜 ℬ e) (p : Proj ℬ) (hp : p ∈ domain ψ) : Proj 𝒜 where
  asHomogeneousIdeal :=
    { __ := p.asHomogeneousIdeal.toIdeal.comap ψ.toRingHom
      is_homogeneous' := sorry }
  isPrime := sorry
  not_irrelevant_le := sorry

/-- The homogeneous ideal of the corresponding point is the inverse image of the original
homogeneous ideal. -/
theorem comapFun_spec (ψ : DegreeMulHom 𝒜 ℬ e) (p : Proj ℬ) (hp : p ∈ domain ψ) :
    (comapFun ψ p hp).asHomogeneousIdeal.toIdeal =
      p.asHomogeneousIdeal.toIdeal.comap ψ.toRingHom := sorry

/-- The corresponding point does not contain the irrelevant ideal of `𝒜`. -/
theorem comapFun_not_irrelevant_le (ψ : DegreeMulHom 𝒜 ℬ e) (p : Proj ℬ)
    (hp : p ∈ domain ψ) :
    ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ (comapFun ψ p hp).asHomogeneousIdeal := sorry

/-- The `e = 1` domain agrees with the ordinary graded `Proj` map domain. -/
theorem domain_eq_projMapDomain (ψ : DegreeMulHom 𝒜 ℬ 1) :
    domain ψ = projMapDomain (toGradedRingHom ψ) := sorry

/-- The homogeneous-fraction representative obtained by applying `ψ` and multiplying
degrees by `e`. -/
def awayMapNumDen (ψ : DegreeMulHom 𝒜 ℬ e) {f : A} (z : Away 𝒜 f) :
    NumDenSameDeg ℬ (Submonoid.powers (ψ.toRingHom f)) where
  deg := z.deg * e
  num := ⟨ψ.toRingHom z.num, ψ.map_mem z.num_mem_deg⟩
  den := ⟨ψ.toRingHom z.den, ψ.map_mem z.den_mem_deg⟩
  den_mem := toRingHom_mem_powers ψ z.den_mem

/-- The map of homogeneous localizations away from `f` and `ψ(f)` induced by a
degree-multiplying homomorphism. -/
def awayMap (ψ : DegreeMulHom 𝒜 ℬ e) (f : A) :
    Away 𝒜 f →+* Away ℬ (ψ.toRingHom f) where
  toFun z := HomogeneousLocalization.mk (awayMapNumDen ψ z)
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- On homogeneous fractions `x / f^n`, `awayMap` applies `ψ` to the numerator and
denominator. -/
theorem awayMap_mk (ψ : DegreeMulHom 𝒜 ℬ e) {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    awayMap ψ f (Away.mk 𝒜 hf n x hx) =
      Away.mk ℬ (ψ.map_mem hf) n (ψ.toRingHom x) (map_mem_nsmul ψ hx) := sorry

/-- The `e = 1` localization map agrees with `Away.map`. -/
theorem awayMap_eq_Away_map (ψ : DegreeMulHom 𝒜 ℬ 1) (f : A) :
    awayMap ψ f = Away.map (toGradedRingHom ψ) f := sorry

/-- The standard-open cover of the induced domain by positive homogeneous basic opens. -/
abbrev openCover (ψ : DegreeMulHom 𝒜 ℬ e) :
    (domain ψ).toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover
    (fun f : PositiveHomogeneous 𝒜 ↦ Proj.basicOpen ℬ (ψ.toRingHom f.val))

/-- The affine-local morphism on a positive homogeneous basic open used to glue the
induced `Proj` map. -/
abbrev basicOpenMap (ψ : DegreeMulHom 𝒜 ℬ e) (f : PositiveHomogeneous 𝒜) :
    (openCover ψ).X f ⟶ Proj 𝒜 :=
  (Proj.basicOpenIsoSpec ℬ (ψ.toRingHom f.val)
      (PositiveHomogeneous.degreeMulMap ψ f).mem_degree
      (PositiveHomogeneous.degreeMulMap ψ f).degree_pos).hom ≫
    Spec.map (CommRingCat.ofHom (awayMap ψ f.val)) ≫
      Proj.awayι 𝒜 f.val f.mem_degree f.degree_pos

/-- The affine-local maps defining the induced `Proj` morphism agree on pairwise overlaps. -/
theorem basicOpenMap_compatible (ψ : DegreeMulHom 𝒜 ℬ e)
    (f g : PositiveHomogeneous 𝒜) :
    pullback.fst ((openCover ψ).f f) ((openCover ψ).f g) ≫ basicOpenMap ψ f =
      pullback.snd ((openCover ψ).f f) ((openCover ψ).f g) ≫
        basicOpenMap ψ g := sorry

/-- The scheme morphism `r_ψ : U ⟶ Proj 𝒜` induced by a degree-multiplying ring map. -/
def map (ψ : DegreeMulHom 𝒜 ℬ e) :
    (domain ψ).toScheme ⟶ Proj 𝒜 :=
  (openCover ψ).glueMorphisms (basicOpenMap ψ) (basicOpenMap_compatible ψ)

/-- The inverse image of a positive homogeneous basic open under the induced morphism is
the corresponding basic open in the target. -/
theorem map_preimage_basicOpen (ψ : DegreeMulHom 𝒜 ℬ e)
    {f : A} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    (domain ψ).ι ''ᵁ (map ψ ⁻¹ᵁ Proj.basicOpen 𝒜 f) =
      Proj.basicOpen ℬ (ψ.toRingHom f) := sorry

/-- Compatibility of a candidate morphism with the homogeneous-localization formula on a
positive homogeneous basic open. -/
abbrev basicOpenCompatibility (ψ : DegreeMulHom 𝒜 ℬ e)
    (g : (domain ψ).toScheme ⟶ Proj 𝒜) {f : A} {d : ℕ}
    (hd : 0 < d) (hf : f ∈ 𝒜 d) : Prop :=
  (Proj.basicOpenIsoSpec ℬ (ψ.toRingHom f) (ψ.map_mem hf)
      (Nat.mul_pos hd (Nat.succ_le_iff.mp ψ.one_le_degree))).inv ≫
    (Proj ℬ).homOfLE (basicOpen_le_domain ψ hd hf) ≫ g =
      Spec.map (CommRingCat.ofHom (awayMap ψ f)) ≫ Proj.awayι 𝒜 f hf hd

/-- On a positive homogeneous basic open, the induced morphism is given by the
corresponding map of homogeneous localizations. -/
theorem map_basicOpenIsoSpec_inv_comp (ψ : DegreeMulHom 𝒜 ℬ e)
    {f : A} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d) :
    basicOpenCompatibility ψ (map ψ) hd hf := sorry

/-- A morphism from the induced domain is the canonical `r_ψ` when it has the prescribed
homogeneous-localization formula on every positive basic open. -/
theorem map_unique (ψ : DegreeMulHom 𝒜 ℬ e)
    (g : (domain ψ).toScheme ⟶ Proj 𝒜)
    (hg : ∀ {f : A} {d : ℕ} (hd : 0 < d) (hf : f ∈ 𝒜 d),
      basicOpenCompatibility ψ g hd hf) :
    g = map ψ := sorry

/-- The `e = 1` glued morphism agrees with the ordinary graded `Proj` map. -/
theorem map_eq_projMapMap (ψ : DegreeMulHom 𝒜 ℬ 1) :
    map ψ =
      ((Proj ℬ).isoOfEq (domain_eq_projMapDomain ψ)).hom ≫
        projMapMap (toGradedRingHom ψ) := sorry

/-- The canonical map from the full target projective spectrum to the induced domain
when that domain is all of `Proj ℬ`. -/
abbrev domainTopInclusion (ψ : DegreeMulHom 𝒜 ℬ e) (hU : domain ψ = ⊤) :
    Proj ℬ ⟶ (domain ψ).toScheme :=
  (Scheme.topIso (Proj ℬ)).inv ≫ ((Proj ℬ).isoOfEq hU.symm).hom

/-- Extending `r_ψ` to a morphism of full projective spectra when the induced domain is
all of `Proj ℬ`. -/
abbrev mapOnTarget (ψ : DegreeMulHom 𝒜 ℬ e) (hU : domain ψ = ⊤) :
    Proj ℬ ⟶ Proj 𝒜 :=
  domainTopInclusion ψ hU ≫ map ψ

end DegreeMulHom

end AlgebraicGeometry
