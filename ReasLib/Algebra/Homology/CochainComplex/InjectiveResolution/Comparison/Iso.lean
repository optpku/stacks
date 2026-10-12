/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution.Comparison

/-!
# Canonical Homotopy Isomorphisms Between Injective Resolutions

Any two injective resolutions of the same complex are canonically isomorphic in the homotopy
category. This file packages the comparison maps into an isomorphism and records its computation,
coherence, and naturality API.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.InjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A compatible map between injective resolutions over an isomorphism of base complexes is an
isomorphism in the homotopy category. -/
theorem isIso_of_isHomotopyMap {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    {u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L} [IsIso u]
    {a : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex}
    (ha : I.IsHomotopyMap J u a) : IsIso a := sorry

/-- The canonical homotopy map between injective resolutions is an isomorphism whenever its
base morphism is an isomorphism. -/
noncomputable instance homotopyMap_isIso {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) [IsIso u] :
    IsIso (I.homotopyMap J u) := sorry

namespace homotopyMapIso

/-- The homotopy maps induced by an isomorphism and its inverse are inverse in the forward
order. -/
theorem hom_inv_id {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    I.homotopyMap J e.hom ≫ J.homotopyMap I e.inv = 𝟙 _ := sorry

/-- The homotopy maps induced by an isomorphism and its inverse are inverse in the reverse
order. -/
theorem inv_hom_id {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    J.homotopyMap I e.inv ≫ I.homotopyMap J e.hom = 𝟙 _ := sorry

end homotopyMapIso

/-- An isomorphism of base complexes induces an isomorphism between any chosen injective
resolutions in the homotopy category. Its morphism data are the canonical homotopy maps over the
forward and inverse base morphisms. -/
@[stacks 013Y "homotopy isomorphism induced on injective resolutions"]
noncomputable def homotopyMapIso {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I.complex ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex where
  hom := I.homotopyMap J e.hom
  inv := J.homotopyMap I e.inv
  hom_inv_id := homotopyMapIso.hom_inv_id I J e
  inv_hom_id := homotopyMapIso.inv_hom_id I J e

namespace homotopyMapIso

/-- The forward morphism of the induced isomorphism is the homotopy map over the forward base
morphism. -/
@[simp]
theorem hom {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyMapIso I J e).hom = I.homotopyMap J e.hom := sorry

/-- The inverse morphism of the induced isomorphism is the homotopy map over the inverse base
morphism. -/
@[simp]
theorem inv {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J : InjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyMapIso I J e).inv = J.homotopyMap I e.inv := sorry

end homotopyMapIso

namespace homotopyComparisonIso

/-- The two canonical comparison maps between injective resolutions are inverse in the
homotopy category. -/
theorem hom_inv_id {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    I.homotopyMap J (𝟙 _) ≫ J.homotopyMap I (𝟙 _) = 𝟙 _ := sorry

/-- The reverse and forward canonical comparison maps between injective resolutions are
inverse in the homotopy category. -/
theorem inv_hom_id {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    J.homotopyMap I (𝟙 _) ≫ I.homotopyMap J (𝟙 _) = 𝟙 _ := sorry

end homotopyComparisonIso

/-- The canonical isomorphism in the homotopy category between two injective resolutions of the
same complex. Its morphism data are the two canonical homotopy maps; only the inverse laws are
proof fields. -/
@[stacks 013Y "canonical comparison isomorphism between injective resolutions"]
noncomputable def homotopyComparisonIso {K : CochainComplex 𝒜 ℤ}
    (I J : InjectiveResolution K) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I.complex ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex :=
  homotopyMapIso I J (Iso.refl _)

namespace homotopyComparisonIso

/-- The forward map of the canonical comparison isomorphism is the canonical comparison map. -/
@[simp]
theorem hom {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (homotopyComparisonIso I J).hom = I.homotopyMap J (𝟙 _) := sorry

/-- The inverse map of the canonical comparison isomorphism is the reverse canonical comparison
map. -/
@[simp]
theorem inv {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (homotopyComparisonIso I J).inv = J.homotopyMap I (𝟙 _) := sorry

/-- The canonical comparison isomorphism commutes with the augmentations. -/
@[reassoc (attr := simp)]
theorem hom_fac {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).map I.ι ≫
        (homotopyComparisonIso I J).hom =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map J.ι := sorry

/-- The inverse canonical comparison isomorphism commutes with the augmentations. -/
@[reassoc (attr := simp)]
theorem inv_fac {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).map J.ι ≫
        (homotopyComparisonIso I J).inv =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map I.ι := sorry

/-- The canonical comparison isomorphism from a resolution to itself is the identity
isomorphism. -/
@[simp]
theorem refl {K : CochainComplex 𝒜 ℤ} (I : InjectiveResolution K) :
    homotopyComparisonIso I I = Iso.refl _ := sorry

/-- Reversing the canonical comparison isomorphism exchanges its two resolutions. -/
@[simp]
theorem symm {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (homotopyComparisonIso I J).symm = homotopyComparisonIso J I := sorry

/-- Canonical comparison isomorphisms are transitive in the chosen resolution. -/
@[simp]
theorem trans {K : CochainComplex 𝒜 ℤ} (I J H : InjectiveResolution K) :
    homotopyComparisonIso I J ≪≫ homotopyComparisonIso J H =
      homotopyComparisonIso I H := sorry

end homotopyComparisonIso

/-- A comparison between two resolutions of the same complex is canonical
precisely when it is the forward map of `homotopyComparisonIso`. -/
@[simp]
theorem isHomotopyComparison_iff {K : CochainComplex 𝒜 ℤ}
    (I J : InjectiveResolution K)
    (a : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj J.complex) :
    I.IsHomotopyComparison J a ↔ a = (homotopyComparisonIso I J).hom := sorry

/-- Comparison maps are natural when either the source or target injective resolution model is
changed by its canonical comparison isomorphism. -/
@[reassoc, stacks 013Y "chosen-model naturality of injective-resolution homotopy maps"]
theorem homotopyMap_naturality {K L : CochainComplex 𝒜 ℤ}
    (I I' : InjectiveResolution K) (J J' : InjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyComparisonIso I I').hom ≫ I'.homotopyMap J' u =
      I.homotopyMap J u ≫ (homotopyComparisonIso J J').hom := sorry

/-- Changing only the source injective resolution acts by precomposition with the canonical
comparison isomorphism. -/
@[reassoc (attr := simp)]
theorem homotopyMap_changeSource {K L : CochainComplex 𝒜 ℤ}
    (I I' : InjectiveResolution K) (J : InjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyComparisonIso I I').hom ≫ I'.homotopyMap J u =
      I.homotopyMap J u := sorry

/-- Changing only the target injective resolution acts by postcomposition with the canonical
comparison isomorphism. -/
@[reassoc (attr := simp)]
theorem homotopyMap_changeTarget {K L : CochainComplex 𝒜 ℤ}
    (I : InjectiveResolution K) (J J' : InjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    I.homotopyMap J u ≫ (homotopyComparisonIso J J').hom =
      I.homotopyMap J' u := sorry

end CochainComplex.InjectiveResolution


