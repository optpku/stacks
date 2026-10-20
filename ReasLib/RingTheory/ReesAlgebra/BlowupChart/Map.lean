module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart

/-!
# Functorial maps of affine blowup charts

A ring map carrying one ideal into another induces a map of affine blowup charts
once the distinguished center elements are compatible.  This file contains only
that functorial interface; tensor-product base change lives in `BaseChange`.
-/

@[expose] public section

noncomputable section

open HomogeneousLocalization
open scoped AffineBlowupChart

universe u v w

namespace AffineBlowupChart

variable {R : Type u} [CommRing R]

/-- The image of an element of a source center in a compatible target center. -/
@[stacks 0BIP "functorial center element"]
def mapElement {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J} (a : I) : J :=
  ⟨f a, hIJ a.property⟩

/-- Coercing a mapped center element recovers its image under the ring map. -/
@[stacks 0BIP "functorial center element coercion", simp]
theorem coe_mapElement {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J} (a : I) :
    (mapElement f I J (hIJ := hIJ) a : S) = f a := sorry

/-- The identity ring map acts trivially on center elements. -/
@[stacks 0BIP "functorial center element identity", simp]
theorem mapElement_id (I : Ideal R) (a : I) :
    mapElement (RingHom.id R) I I (hIJ := (Ideal.comap_id I).symm.le) a = a := sorry

namespace map

/-- Powers of a distinguished source element map to powers of a compatible target element. -/
@[stacks 0BIP "functorial chart denominator powers"]
theorem denominatorPowers_le
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (a : I) (b : J) {hab : f a = b} :
    Submonoid.powers (ReesAlgebra.Grading.degreeOne I a) ≤
      (Submonoid.powers (ReesAlgebra.Grading.degreeOne J b)).comap
        (ReesAlgebra.Grading.gradedMap f I J (hIJ := hIJ)) := sorry

/-- Compatibility of centers is closed under composition of ring maps. -/
@[stacks 0BIP "functorial center composition"]
theorem comp_center_le
    {S : Type v} [CommRing S] {T : Type w} [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T)
    {hIJ : I ≤ Ideal.comap f J} {hJK : J ≤ Ideal.comap g K} :
    I ≤ Ideal.comap (g.comp f) K := sorry

/-- Compatible distinguished center elements remain compatible under composition. -/
@[stacks 0BIP "functorial distinguished element composition"]
theorem comp_element_eq
    {S : Type v} [CommRing S] {T : Type w} [CommRing T]
    (f : R →+* S) (g : S →+* T)
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    (a : I) (b : J) (c : K) {hab : f a = b} {hbc : g b = c} :
    (g.comp f) a = c := sorry

end map

/-- Mapped center elements are compatible with composition of ring maps. -/
@[stacks 0BIP "functorial center element composition", simp]
theorem mapElement_comp
    {S : Type v} [CommRing S] {T : Type w} [CommRing T]
    (f : R →+* S) (g : S →+* T)
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    {hIJ : I ≤ Ideal.comap f J} {hJK : J ≤ Ideal.comap g K}
    (a : I) :
    mapElement (g.comp f) I K
        (hIJ := map.comp_center_le f g I J K (hIJ := hIJ) (hJK := hJK)) a =
      mapElement g J K (hIJ := hJK)
        (mapElement f I J (hIJ := hIJ) a) := sorry

/-- The ring map between affine blowup charts induced by compatible center data. -/
@[stacks 0BIP "functorial affine blowup chart map"]
noncomputable def map
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (a : I) (b : J) {hab : f a = b} : R[I / a] →+* S[J / b] :=
  HomogeneousLocalization.map (ReesAlgebra.Grading.gradedMap f I J (hIJ := hIJ))
    (map.denominatorPowers_le f I J (hIJ := hIJ) a b (hab := hab))

/-- A functorial affine-chart map agrees with its underlying map on source scalars. -/
@[stacks 0BIP "functorial chart map on scalars", simp]
theorem map_algebraMap
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (a : I) (b : J) {hab : f a = b} (r : R) :
    map f I J (hIJ := hIJ) a b (hab := hab)
        (@algebraMap R R[I / a] _ _ (instAlgebra I a) r) =
      @algebraMap S S[J / b] _ _ (instAlgebra J b) (f r) := sorry

/-- A functorial affine-chart map sends a basic fraction to the corresponding target
fraction. -/
@[stacks 0BIP "functorial chart map on basic fractions", simp]
theorem map_basicFraction
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (a : I) (b : J) {hab : f a = b} (x : I) :
    map f I J (hIJ := hIJ) a b (hab := hab)
        (AffineBlowupChart.basicFraction I a x) =
      AffineBlowupChart.basicFraction J b (mapElement f I J (hIJ := hIJ) x) := sorry

/-- The image of a numerator in `I ^ n` under a compatible ring map. -/
@[stacks 0BIP "functorial power numerator"]
def mapPowerElement
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (n : ℕ) (x : ↥(I ^ n)) : ↥(J ^ n) :=
  ⟨f x.1, (Ideal.pow_right_mono hIJ n).trans (J.le_comap_pow f n) x.2⟩

/-- Coercion of a mapped power numerator is the ordinary image under the ring map. -/
@[stacks 0BIP "functorial power numerator coercion", simp]
theorem coe_mapPowerElement
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (n : ℕ) (x : ↥(I ^ n)) :
    (mapPowerElement f I J (hIJ := hIJ) n x : S) = f x.1 := sorry

/-- The identity ring map acts trivially on power numerators. -/
@[stacks 0BIP "functorial power numerator identity", simp]
theorem mapPowerElement_id (I : Ideal R) (n : ℕ) (x : ↥(I ^ n)) :
    mapPowerElement (RingHom.id R) I I
        (hIJ := (Ideal.comap_id I).symm.le) n x = x := sorry

/-- Mapped power numerators are compatible with composition of ring maps. -/
@[stacks 0BIP "functorial power numerator composition"]
theorem mapPowerElement_comp
    {S : Type v} [CommRing S] {T : Type w} [CommRing T]
    (f : R →+* S) (g : S →+* T)
    {I : Ideal R} {J : Ideal S} {K : Ideal T}
    {hIJ : I ≤ Ideal.comap f J} {hJK : J ≤ Ideal.comap g K}
    (n : ℕ) (x : ↥(I ^ n)) :
    mapPowerElement (g.comp f) I K
        (hIJ := map.comp_center_le f g I J K (hIJ := hIJ) (hJK := hJK)) n x =
      mapPowerElement g J K (hIJ := hJK) n
        (mapPowerElement f I J (hIJ := hIJ) n x) := sorry

/-- A functorial affine-chart map sends a normalized power fraction to the corresponding target
power fraction. -/
@[stacks 0BIP "functorial affine blowup chart power fraction", simp]
theorem map_powerFraction
    {S : Type v} [CommRing S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f J}
    (a : I) (b : J) {hab : f a = b} (n : ℕ) (x : ↥(I ^ n)) :
    map f I J (hIJ := hIJ) a b (hab := hab)
        (AffineBlowupChart.powerFraction I a n x) =
      AffineBlowupChart.powerFraction J b n
        (mapPowerElement f I J (hIJ := hIJ) n x) := sorry

/-- The affine-chart map induced by the identity ring map is the identity. -/
@[stacks 0BIP "functorial chart map identity", simp]
theorem map_id (I : Ideal R) (a : I) :
    map (RingHom.id R) I I (hIJ := (Ideal.comap_id I).symm.le)
        a a (hab := rfl) =
      RingHom.id R[I / a] := sorry

/-- Affine-chart maps respect composition of compatible ring maps. -/
@[stacks 0BIP "functorial chart map composition"]
theorem map_comp
    {S : Type v} [CommRing S] {T : Type w} [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (I : Ideal R) (J : Ideal S) (K : Ideal T)
    {hIJ : I ≤ Ideal.comap f J} {hJK : J ≤ Ideal.comap g K}
    (a : I) (b : J) (c : K) {hab : f a = b} {hbc : g b = c} :
    map (g.comp f) I K
        (hIJ := map.comp_center_le f g I J K (hIJ := hIJ) (hJK := hJK))
        a c (hab := map.comp_element_eq f g a b c (hab := hab) (hbc := hbc)) =
      (map g J K (hIJ := hJK) b c (hab := hbc)).comp
        (map f I J (hIJ := hIJ) a b (hab := hab)) := sorry

/-- The affine-chart map induced by an algebra map commutes with base scalars. -/
@[stacks 0BIP "functorial chart algebra map on scalars"]
theorem mapₐ_commutes
    {A : Type w} [CommRing A] {S : Type v} [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f.toRingHom J}
    (a : I) (b : J) {hab : f a = b} (r : A) :
    map f.toRingHom I J (hIJ := hIJ) a b (hab := hab)
        (@algebraMap A R[I / a] _ _ (instAlgebraOfTower I a) r) =
      @algebraMap A S[J / b] _ _ (instAlgebraOfTower J b) r := sorry

/-- The algebra map between affine blowup charts induced by compatible center data. -/
@[stacks 0BIP "functorial affine blowup chart algebra map"]
noncomputable def mapₐ
    {A : Type w} [CommRing A] {S : Type v} [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f.toRingHom J}
    (a : I) (b : J) {hab : f a = b} : R[I / a] →ₐ[A] S[J / b] where
  toRingHom := map f.toRingHom I J (hIJ := hIJ) a b (hab := hab)
  commutes' := mapₐ_commutes f I J (hIJ := hIJ) a b (hab := hab)

/-- Forgetting scalars from a functorial affine-chart algebra map recovers the underlying ring
map. -/
@[stacks 0BIP "functorial chart algebra map coercion", simp]
theorem mapₐ_apply
    {A : Type w} [CommRing A] {S : Type v} [CommRing S]
    [Algebra A R] [Algebra A S] (f : R →ₐ[A] S)
    (I : Ideal R) (J : Ideal S) {hIJ : I ≤ Ideal.comap f.toRingHom J}
    (a : I) (b : J) {hab : f a = b} (x : R[I / a]) :
    mapₐ f I J (hIJ := hIJ) a b (hab := hab) x =
      map f.toRingHom I J (hIJ := hIJ) a b (hab := hab) x := sorry

end AffineBlowupChart
