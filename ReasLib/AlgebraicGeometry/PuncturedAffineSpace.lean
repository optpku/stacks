/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Punctured affine spaces

This file relates mathlib's relative affine-space model to the polynomial
prime-spectrum model, and owns the zero section and its open complement.
-/

@[expose] public section

open PrimeSpectrum CategoryTheory Opposite
open scoped AlgebraicGeometry PrimeSpectrum

noncomputable section

universe u v

namespace AlgebraicGeometry.PuncturedAffineSpace

section CoordinateModel

variable (ι : Type v) (k : Type u) [CommRing k]

/-- The polynomial coordinate ring of affine space with coordinate type `ι`. -/
@[stacks 01IL "polynomial coordinate ring", stacks 01JD "affine-space coordinate ring",
  stacks 01K8 "infinite affine-space coordinate ring", stacks 01KL "doubled-affine coordinate ring",
  stacks 01KX "punctured-projective coordinate ring"]
abbrev coordinateRing : Type (max u v) := MvPolynomial ι k

/-- The prime-spectrum coordinate model of affine space. -/
@[stacks 01IL "polynomial spectrum model", stacks 01JD "polynomial affine-space model",
  stacks 01K8 "infinite polynomial spectrum", stacks 01KL "doubled-affine underlying model",
  stacks 01KX "punctured projective-space source model"]
abbrev coordinateSpectrum : Scheme.{max u v} :=
  Spec (CommRingCat.of (coordinateRing ι k))

/-- The coordinate function indexed by `i`. -/
@[stacks 01IL "affine coordinate function", stacks 01JD "affine-space coordinate",
  stacks 01K8 "infinite affine-space coordinate", stacks 01KL "doubled-affine coordinate",
  stacks 01KX "punctured-projective coordinate"]
abbrev coordinate (i : ι) : coordinateRing ι k := MvPolynomial.X i

/-- Evaluation at the origin as a `k`-algebra homomorphism, sending every coordinate to zero. -/
@[stacks 01IL "affine-origin algebra map", stacks 01JD "zero-section evaluation algebra map",
  stacks 01K8 "origin evaluation algebra map", stacks 01KL "doubled-affine origin evaluation",
  stacks 01KX "punctured-origin evaluation"]
abbrev evalAtOriginAlgHom : coordinateRing ι k →ₐ[k] k :=
  MvPolynomial.eval₂AlgHom k (fun _ ↦ 0)

/-- The ring-hom view of evaluation at the origin. -/
@[stacks 01IL "affine-origin ring map", stacks 01JD "zero-section evaluation",
  stacks 01K8 "origin evaluation", stacks 01KL "doubled-affine origin evaluation",
  stacks 01KX "punctured-origin evaluation"]
abbrev evalAtOrigin : coordinateRing ι k →+* k :=
  (evalAtOriginAlgHom ι k).toRingHom

/-- The underlying ring homomorphism of the origin-evaluation algebra map is
`evalAtOrigin`. -/
@[simp, stacks 01IL "affine-origin algebra/ring map bridge",
  stacks 01JD "zero-section evaluation algebra/ring map bridge"]
theorem evalAtOriginAlgHom_toRingHom :
    (evalAtOriginAlgHom ι k).toRingHom = evalAtOrigin ι k := sorry

/-- Evaluation at the origin fixes coefficients from the base ring. -/
@[simp, stacks 01IL "affine-origin evaluation on coefficients",
  stacks 01JD "zero-section evaluation on coefficients"]
theorem evalAtOriginAlgHom_algebraMap (r : k) :
    evalAtOriginAlgHom ι k (algebraMap k (coordinateRing ι k) r) = r := sorry

/-- Evaluation at the origin is surjective as a `k`-algebra homomorphism. -/
@[stacks 01IL "affine-origin algebra map is surjective",
  stacks 01JD "zero-section evaluation algebra map is surjective"]
theorem evalAtOriginAlgHom_surjective :
    Function.Surjective (evalAtOriginAlgHom ι k) := sorry

/-- Evaluation at the origin is surjective. -/
@[stacks 01JD "zero-section evaluation is surjective",
  stacks 01K8 "origin evaluation is surjective"]
theorem evalAtOrigin_surjective :
    Function.Surjective (evalAtOrigin ι k) := sorry

/-- Evaluation at the origin sends every coordinate function to zero. -/
@[simp, stacks 01JD "coordinates vanish at the zero section",
  stacks 01K8 "coordinates vanish at the origin"]
theorem evalAtOrigin_coordinate (i : ι) :
    evalAtOrigin ι k (coordinate ι k i) = 0 := sorry

/-- The origin-evaluation algebra map sends every coordinate function to zero. -/
@[simp, stacks 01IL "coordinates vanish at the affine origin",
  stacks 01JD "coordinates vanish under the zero-section algebra map"]
theorem evalAtOriginAlgHom_coordinate (i : ι) :
    evalAtOriginAlgHom ι k (coordinate ι k i) = 0 := sorry

/-- The ideal of polynomial functions vanishing at the origin. -/
@[stacks 01JD "zero-section ideal", stacks 01K8 "origin ideal", stacks 01KX "punctured origin ideal"]
def originIdeal : Ideal (coordinateRing ι k) :=
  RingHom.ker (evalAtOrigin ι k)

/-- A polynomial belongs to the origin ideal exactly when its value at the origin is zero. -/
@[simp, stacks 01IL "affine-origin ideal membership",
  stacks 01JD "zero-section ideal membership", stacks 01K8 "origin ideal membership"]
theorem mem_originIdeal_iff (p : coordinateRing ι k) :
    p ∈ originIdeal ι k ↔ evalAtOriginAlgHom ι k p = 0 := sorry

/-- Every coordinate function belongs to the origin ideal. -/
@[stacks 01JD "coordinates lie in the zero-section ideal",
  stacks 01K8 "coordinates lie in the origin ideal"]
theorem coordinate_mem_originIdeal (i : ι) :
    coordinate ι k i ∈ originIdeal ι k := sorry

/-- The origin ideal is generated by all coordinate functions. -/
@[stacks 01JD "zero-section ideal generators", stacks 01K8 "origin ideal generators",
  stacks 01KL "doubled-affine ideal generators"]
theorem originIdeal_eq_span :
    originIdeal ι k =
      Ideal.span (Set.range (coordinate ι k) : Set (coordinateRing ι k)) := sorry

/-- The punctured open in the coordinate model, as the union of all coordinate basic opens. -/
@[stacks 01IL "coordinate punctured affine space", stacks 01JD "punctured affine-space overlap",
  stacks 01K8 "punctured infinite spectrum", stacks 01KL "punctured doubled-affine overlap",
  stacks 01KX "punctured projective-space source"]
def coordinatePuncturedOpen : (coordinateSpectrum ι k).Opens :=
  ⨆ i : ι, D(coordinate ι k i)

/-- Every coordinate basic open is contained in the punctured open. -/
@[stacks 01IL "coordinate basic open lies in the puncture",
  stacks 01K8 "coordinate basic open lies in the infinite puncture"]
theorem basicOpen_coordinate_le_coordinatePuncturedOpen (i : ι) :
    D(coordinate ι k i) ≤ coordinatePuncturedOpen ι k := sorry

/-- In the coordinate model, the punctured open is the complement of the origin ideal's zero
locus. -/
@[stacks 01IL "coordinate puncture as a zero-locus complement",
  stacks 01K8 "puncture as the complement of the origin zero locus"]
theorem coordinatePuncturedOpen.coe_eq_compl_zeroLocus :
    (coordinatePuncturedOpen ι k : Set (coordinateSpectrum ι k)) =
      V((originIdeal ι k : Set (coordinateRing ι k)))ᶜ := sorry

end CoordinateModel

section CoordinateZeroSection

variable (ι : Type u) (k : Type u) [CommRing k]

/-- The structure morphism of the coordinate-spectrum model. -/
@[stacks 01IL "coordinate-spectrum structure morphism", stacks 01JD "affine-space structure morphism",
  stacks 01K8 "infinite affine-space structure morphism", stacks 01KL "doubled-affine structure morphism",
  stacks 01KX "punctured-projective structure morphism"]
noncomputable abbrev coordinateSpectrumToBase :
    coordinateSpectrum ι k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* coordinateRing ι k))

/-- The zero section of the coordinate-spectrum model. -/
@[stacks 01JD "coordinate zero section", stacks 01K8 "coordinate origin section",
  stacks 01KL "doubled-affine zero section", stacks 01KX "punctured-origin section"]
noncomputable abbrev coordinateZeroSection :
    Spec (CommRingCat.of k) ⟶ coordinateSpectrum ι k :=
  Spec.map (CommRingCat.ofHom (evalAtOrigin ι k))

/-- The coordinate-model zero section is a closed immersion. -/
@[stacks 01JD "coordinate zero section closed immersion", stacks 01K8 "origin section closed immersion",
  stacks 01KL "doubled-affine zero section closed immersion"]
instance coordinateZeroSection_isClosedImmersion :
    IsClosedImmersion (coordinateZeroSection ι k) := sorry

/-- The coordinate-model zero section is a section of the structure morphism. -/
@[reassoc (attr := simp), stacks 01JD "coordinate zero section structure map",
  stacks 01K8 "origin section structure map", stacks 01KL "doubled-affine zero section structure map"]
theorem coordinateZeroSection_coordinateSpectrumToBase :
    coordinateZeroSection ι k ≫ coordinateSpectrumToBase ι k = 𝟙 _ := sorry

/-- The zero section has image the zero locus of the coordinate ideal. -/
@[stacks 01JD "coordinate zero-section image", stacks 01K8 "origin-section image",
  stacks 01KL "doubled-affine zero-section image"]
theorem range_coordinateZeroSection :
    Set.range (coordinateZeroSection ι k).base =
      V((originIdeal ι k : Set (coordinateRing ι k))) := sorry

/-- The coordinate-model punctured open is the complement of the zero-section image. -/
@[stacks 01IL "coordinate puncture complement", stacks 01JD "affine-space puncture complement",
  stacks 01K8 "infinite puncture complement", stacks 01KL "doubled-affine puncture complement"]
theorem coordinatePuncturedOpen.coe_eq_compl_range_coordinateZeroSection :
    (coordinatePuncturedOpen ι k : Set (coordinateSpectrum ι k)) =
      (Set.range (coordinateZeroSection ι k).base)ᶜ := sorry

end CoordinateZeroSection

section CoordinateOrigin

variable (ι : Type v) (k : Type u) [CommRing k] [IsDomain k]

/-- The origin point in the coordinate model, represented by the prime kernel of evaluation. -/
@[stacks 01IL "coordinate origin", stacks 01JD "coordinate affine-space origin",
  stacks 01K8 "coordinate infinite origin", stacks 01KL "coordinate doubled-affine origin"]
def coordinateOrigin : PrimeSpectrum (coordinateRing ι k) :=
  ⟨originIdeal ι k, RingHom.ker_isPrime (evalAtOrigin ι k)⟩

/-- The prime ideal underlying the coordinate-model origin is the origin ideal. -/
@[simp, stacks 01IL "coordinate origin ideal",
  stacks 01K8 "origin point ideal"]
theorem coordinateOrigin_asIdeal :
    (coordinateOrigin ι k).asIdeal = originIdeal ι k := sorry

end CoordinateOrigin

section CoordinateField

variable (ι : Type v) (k : Type u) [Field k]

/-- The ideal generated by all coordinate functions is the maximal ideal of the
origin over a field. -/
@[stacks 01K8 "maximal ideal of the origin", stacks 01KL "maximal ideal of the origin",
  instance]
theorem originIdeal_isMaximal : (originIdeal ι k).IsMaximal := sorry

/-- Over a field, the coordinate-model punctured open is the complement of its origin. -/
@[stacks 01K8 "coordinate puncture as the complement of the origin",
  stacks 01KL "coordinate puncture as the complement of the origin"]
theorem coordinatePuncturedOpen.coe_eq_compl_coordinateOrigin :
    (coordinatePuncturedOpen ι k : Set (coordinateSpectrum ι k)) =
      ({coordinateOrigin ι k} : Set (coordinateSpectrum ι k))ᶜ := sorry

/-- In the coordinate model over a field, punctured-open membership means being nonzero. -/
@[simp, stacks 01K8 "coordinate puncture membership",
  stacks 01KL "coordinate puncture membership"]
theorem coordinatePuncturedOpen.mem_iff_ne_coordinateOrigin
    (x : coordinateSpectrum ι k) :
    x ∈ coordinatePuncturedOpen ι k ↔ x ≠ coordinateOrigin ι k := sorry

end CoordinateField

section CanonicalModel

variable (ι : Type u) (k : Type u) [CommRing k]

/-- Affine space over `Spec(k)` in mathlib's canonical relative `AffineSpace` model. -/
@[stacks 01IL "relative affine-plane model", stacks 01JD "relative affine-space model",
  stacks 01K8 "relative infinite affine space", stacks 01KL "relative doubled-affine model",
  stacks 01KX "relative punctured-projective source"]
abbrev affineSpace : Scheme.{u} :=
  𝔸(ULift.{u} ι; Spec (CommRingCat.of k))

/-- The canonical structure morphism `𝔸^ι_k ⟶ Spec(k)`. -/
@[stacks 01IL "relative affine-space structure morphism", stacks 01JD "affine-space structure morphism",
  stacks 01K8 "infinite affine-space structure morphism", stacks 01KL "doubled-affine structure morphism",
  stacks 01KX "punctured-projective structure morphism"]
abbrev toBase : affineSpace ι k ⟶ Spec (CommRingCat.of k) :=
  affineSpace ι k ↘ Spec (CommRingCat.of k)

/-- The canonical comparison from relative affine space to its polynomial coordinate spectrum. -/
@[stacks 01IL "affine-space/polynomial-spectrum comparison", stacks 01JD "affine-space comparison",
  stacks 01K8 "infinite affine-space comparison", stacks 01KL "doubled-affine comparison",
  stacks 01KX "punctured-projective affine-space comparison"]
noncomputable def coordinateModelIso :
    affineSpace ι k ≅ coordinateSpectrum ι k :=
  AffineSpace.SpecIso (ULift.{u} ι) (CommRingCat.of k) ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.renameEquiv k
        (Equiv.ulift : ULift.{u} ι ≃ ι)).symm.toRingEquiv.toCommRingCatIso.op

namespace coordinateModelIso

/-- The affine-space comparison respects the structure morphisms to `Spec(k)`. -/
@[reassoc, stacks 01IL "affine-space comparison over the base",
  stacks 01JD "affine-space comparison over the base"]
theorem hom_toBase :
    (coordinateModelIso ι k).hom ≫ coordinateSpectrumToBase ι k =
      toBase ι k := sorry

end coordinateModelIso

/-- The polynomial coordinate ring is canonically isomorphic to global sections of relative
affine space. -/
@[stacks 01IL "affine-space global-sections model", stacks 01JD "affine-space global-sections model",
  stacks 01K8 "infinite affine-space global sections", stacks 01KL "doubled-affine global sections",
  stacks 01KX "punctured-projective global sections"]
noncomputable def coordinateRingGlobalSectionsIso :
    CommRingCat.of (coordinateRing ι k) ≅ Scheme.Γ.obj (op (affineSpace ι k)) :=
  (Scheme.ΓSpecIso (CommRingCat.of (coordinateRing ι k))).symm ≪≫
    Scheme.Γ.mapIso (coordinateModelIso ι k).op

/-- The forward map of `coordinateRingGlobalSectionsIso`. -/
@[stacks 01IL "coordinate-to-global-sections map", stacks 01JD "affine-space coordinate-to-sections map",
  stacks 01K8 "infinite coordinate-to-sections map", stacks 01KL "doubled-affine coordinate-to-sections map"]
noncomputable abbrev coordinateRingToGlobalSections :
    CommRingCat.of (coordinateRing ι k) ⟶ Scheme.Γ.obj (op (affineSpace ι k)) :=
  (coordinateRingGlobalSectionsIso ι k).hom

/-- The `i`-th global coordinate section on canonical affine space. -/
@[stacks 01IL "global affine coordinate section", stacks 01JD "global affine-space coordinate section",
  stacks 01K8 "global infinite coordinate section", stacks 01KL "global doubled-affine coordinate section"]
noncomputable abbrev coordinateSection (i : ι) : Γ(affineSpace ι k, ⊤) :=
  coordinateRingToGlobalSections ι k (coordinate ι k i)

/-- Constants map through the affine-space structure morphism. -/
@[stacks 01IL "global-sections constants", stacks 01JD "affine-space constants",
  stacks 01K8 "infinite affine-space constants", stacks 01KL "doubled-affine constants"]
theorem coordinateRingToGlobalSections_C (r : k) :
    coordinateRingToGlobalSections ι k (MvPolynomial.C r) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Γ.map (toBase ι k).op) r := sorry

/-- The transported coordinate agrees with mathlib's affine-space coordinate. -/
@[stacks 01IL "affine coordinate comparison", stacks 01JD "affine-space coordinate comparison",
  stacks 01K8 "infinite coordinate comparison", stacks 01KL "doubled-affine coordinate comparison"]
theorem coordinateSection_eq_affineSpace_coord (i : ι) :
    coordinateSection ι k i =
      AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i) := sorry

/-- The zero section of canonical relative affine space. -/
@[stacks 01JD "zero section", stacks 01K8 "origin zero section", stacks 01KL "doubled-affine zero section"]
noncomputable def zeroSection : Spec (CommRingCat.of k) ⟶ affineSpace ι k :=
  AffineSpace.homOfVector (𝟙 _) (fun _ ↦ 0)

namespace coordinateModelIso

/-- The comparison carries the canonical zero section to evaluation at the origin. -/
@[reassoc, stacks 01JD "zero section under the affine-space comparison"]
theorem zeroSection_hom :
    zeroSection ι k ≫ (coordinateModelIso ι k).hom =
      coordinateZeroSection ι k := sorry

end coordinateModelIso

/-- The canonical zero section is a section of the affine-space structure morphism. -/
@[reassoc (attr := simp), stacks 01JD "zero section is a section"]
theorem zeroSection_toBase : zeroSection ι k ≫ toBase ι k = 𝟙 _ := sorry

/-- The zero section of affine space is a closed immersion. -/
@[stacks 01JD "affine-space zero section closed immersion", stacks 01K8 "origin section closed immersion",
  stacks 01KL "doubled-affine zero section closed immersion"]
instance zeroSection_isClosedImmersion :
    IsClosedImmersion (zeroSection ι k) := sorry

/-- Punctured affine space in the canonical relative `AffineSpace` model. -/
@[stacks 01IL "punctured affine space", stacks 01JD "punctured affine-space overlap",
  stacks 01K8 "punctured infinite affine space", stacks 01KL "punctured doubled-affine overlap",
  stacks 01KX "punctured projective-space source"]
def puncturedOpen : (affineSpace ι k).Opens :=
  ⨆ i : ι, (affineSpace ι k).basicOpen (coordinateSection ι k i)

namespace coordinateModelIso

/-- The affine-space comparison pulls the coordinate puncture back to canonical punctured
affine space. -/
@[stacks 01IL "punctured affine-space transport", stacks 01JD "punctured affine-space transport",
  stacks 01K8 "punctured infinite-affine transport", stacks 01KL "doubled-affine overlap transport",
  stacks 01KX "punctured projective-space transport", simp]
theorem preimage_puncturedOpen :
    (coordinateModelIso ι k).hom ⁻¹ᵁ coordinatePuncturedOpen ι k =
      puncturedOpen ι k := sorry

end coordinateModelIso

/-- Canonical punctured affine space is the complement of the zero-section image. -/
@[stacks 01IL "punctured affine-space zero-section complement",
  stacks 01K8 "punctured infinite zero-section complement",
  stacks 01KL "doubled-affine zero-section complement"]
theorem puncturedOpen.coe_eq_compl_range_zeroSection :
    (puncturedOpen ι k : Set (affineSpace ι k)) =
      (Set.range (zeroSection ι k).base)ᶜ := sorry

/-- The canonical map from the polynomial coordinate ring to global sections of punctured
affine space. -/
@[stacks 01IL "punctured-affine global-sections comparison"]
noncomputable abbrev globalSectionsComparison :
    CommRingCat.of (coordinateRing ι k) ⟶
      Scheme.Γ.obj (Opposite.op (puncturedOpen ι k).toScheme) :=
  coordinateRingToGlobalSections ι k ≫
    Scheme.Γ.map (puncturedOpen ι k).ι.op

end CanonicalModel

section AtLeastTwoCoordinates

variable (ι : Type u) (k : Type u) [CommRing k]

namespace globalSectionsComparison

/-- Two distinct coordinates imply that the punctured-affine global-sections comparison is
invertible. -/
@[stacks 01IL "global sections"]
theorem isIso_of_coordinates (i j : ι) (hij : i ≠ j) :
    IsIso (globalSectionsComparison ι k) := sorry

/-- For a nontrivial coordinate family, restriction to punctured affine space preserves the
global coordinate ring. -/
@[stacks 01IL "global sections"]
theorem isIso [Nontrivial ι] :
    IsIso (globalSectionsComparison ι k) := sorry

end globalSectionsComparison

end AtLeastTwoCoordinates

section CanonicalField

variable (ι : Type u) (k : Type u) [Field k]

/-- The origin point of canonical affine space over a field. -/
@[stacks 01IL "affine-plane origin", stacks 01JD "affine-space origin",
  stacks 01K8 "infinite affine-space origin", stacks 01KL "doubled-affine origin"]
noncomputable def origin : affineSpace ι k :=
  zeroSection ι k (IsLocalRing.closedPoint k)

namespace coordinateModelIso

/-- The affine-space comparison carries the geometric origin to the prime kernel of evaluation. -/
@[stacks 01IL "affine-space origin comparison", stacks 01JD "affine-space origin comparison",
  stacks 01K8 "infinite affine-space origin comparison",
  stacks 01KL "doubled-affine origin comparison"]
theorem hom_origin :
    (coordinateModelIso ι k).hom (origin ι k) =
      coordinateOrigin ι k := sorry

end coordinateModelIso

/-- Over a field, canonical punctured affine space is the complement of the origin. -/
@[stacks 01K8 "puncture as the complement of the origin",
  stacks 01KL "puncture as the complement of the origin"]
theorem puncturedOpen.coe_eq_compl_origin :
    (puncturedOpen ι k : Set (affineSpace ι k)) =
      ({origin ι k} : Set (affineSpace ι k))ᶜ := sorry

/-- A point lies in the punctured open exactly when it is not the origin. -/
@[simp, stacks 01IL "punctured affine-space origin membership",
  stacks 01K8 "punctured infinite origin membership",
  stacks 01KL "doubled-affine origin membership"]
theorem puncturedOpen.mem_iff_ne_origin (x : affineSpace ι k) :
    x ∈ puncturedOpen ι k ↔ x ≠ origin ι k := sorry

/-- With two distinct coordinates, punctured affine space over a field is not affine. -/
@[stacks 01IL "nonaffineness", stacks 01JD "punctured affine space is not affine"]
theorem puncturedOpen_not_isAffine_of_coordinates (i j : ι) (hij : i ≠ j) :
    ¬ IsAffine (puncturedOpen ι k).toScheme := sorry

/-- A nontrivial coordinate family has nonaffine punctured affine space. -/
@[stacks 01IL "nonaffineness", stacks 01JD "punctured affine space is not affine"]
theorem puncturedOpen_not_isAffine [Nontrivial ι] :
    ¬ IsAffine (puncturedOpen ι k).toScheme := sorry

/-- A chosen coordinate witnesses that the punctured affine open is not closed. -/
@[stacks 01KL "punctured affine open is not closed",
  stacks 0FXT "punctured affine line is not closed"]
theorem puncturedOpen_not_isClosed_of_coordinate (i : ι) :
    ¬ IsClosed (puncturedOpen ι k : Set (affineSpace ι k)) := sorry

end CanonicalField

end AlgebraicGeometry.PuncturedAffineSpace
