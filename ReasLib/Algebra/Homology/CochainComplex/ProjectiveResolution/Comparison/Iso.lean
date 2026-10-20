module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Comparison

/-!
# Canonical Homotopy Isomorphisms Between Projective Resolutions

Two projective resolutions of the same cochain complex are canonically isomorphic in the homotopy
category.  The forward and inverse morphisms are the canonical homotopy maps over the identity;
this leaf records their computations, coherence, and naturality under changing chosen models.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

universe v u

namespace CochainComplex.ProjectiveResolution

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A compatible map between projective resolutions over an isomorphism of base complexes is an
isomorphism in the homotopy category. -/
theorem isIso_of_isHomotopyMap {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    {u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L} [IsIso u]
    {a : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Q.complex}
    (ha : P.IsHomotopyMap Q u a) : IsIso a := sorry

/-- The canonical homotopy map between projective resolutions is an isomorphism whenever its
base morphism is an isomorphism. -/
noncomputable instance homotopyMap_isIso {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) [IsIso u] :
    IsIso (P.homotopyMap Q u) := sorry

namespace homotopyMapIso

/-- The homotopy maps induced by an isomorphism and its inverse are inverse in the forward
order. -/
theorem hom_inv_id {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyMap Q e.hom ≫ Q.homotopyMap P e.inv = 𝟙 _ := sorry

/-- The homotopy maps induced by an isomorphism and its inverse are inverse in the reverse
order. -/
theorem inv_hom_id {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    Q.homotopyMap P e.inv ≫ P.homotopyMap Q e.hom = 𝟙 _ := sorry

end homotopyMapIso

/-- An isomorphism of base complexes induces an isomorphism between any chosen projective
resolutions in the homotopy category. Its morphism data are the canonical homotopy maps over the
forward and inverse base morphisms. -/
@[stacks 0648 "homotopy isomorphism induced on projective resolutions"]
noncomputable def homotopyMapIso {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Q.complex where
  hom := P.homotopyMap Q e.hom
  inv := Q.homotopyMap P e.inv
  hom_inv_id := homotopyMapIso.hom_inv_id P Q e
  inv_hom_id := homotopyMapIso.inv_hom_id P Q e

namespace homotopyMapIso

/-- The forward morphism of the induced isomorphism is the homotopy map over the forward base
morphism. -/
@[simp]
theorem hom {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyMapIso P Q e).hom = P.homotopyMap Q e.hom := sorry

/-- The inverse morphism of the induced isomorphism is the homotopy map over the inverse base
morphism. -/
@[simp]
theorem inv {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (e : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyMapIso P Q e).inv = Q.homotopyMap P e.inv := sorry

end homotopyMapIso

namespace homotopyComparisonIso

/-- The two canonical comparison maps between projective resolutions are inverse in the
homotopy category. -/
theorem hom_inv_id {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    P.homotopyMap Q (𝟙 _) ≫ Q.homotopyMap P (𝟙 _) = 𝟙 _ := sorry

/-- The reverse and forward canonical comparison maps between projective resolutions are
inverse in the homotopy category. -/
theorem inv_hom_id {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    Q.homotopyMap P (𝟙 _) ≫ P.homotopyMap Q (𝟙 _) = 𝟙 _ := sorry

end homotopyComparisonIso

/-- The canonical homotopy-category isomorphism between two projective resolutions of the same
cochain complex. Its morphism data are the two canonical homotopy maps; only the inverse laws
are proof fields. -/
@[stacks 0648 "canonical isomorphism between projective resolutions"]
noncomputable def homotopyComparisonIso {K : CochainComplex 𝒜 ℤ}
    (P Q : ProjectiveResolution K) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ≅
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Q.complex :=
  homotopyMapIso P Q (Iso.refl _)

namespace homotopyComparisonIso

/-- The forward morphism of the canonical comparison is the canonical homotopy map over the
identity. -/
@[simp]
theorem hom {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    (homotopyComparisonIso P Q).hom = P.homotopyMap Q (𝟙 _) := sorry

/-- The inverse morphism of the canonical comparison is the reverse canonical homotopy map over
the identity. -/
@[simp]
theorem inv {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    (homotopyComparisonIso P Q).inv = Q.homotopyMap P (𝟙 _) := sorry

/-- The forward canonical comparison intertwines the two projective-resolution comparisons. -/
@[reassoc (attr := simp)]
theorem hom_fac {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    (homotopyComparisonIso P Q).hom ≫
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map Q.π =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map P.π := sorry

/-- The inverse canonical comparison intertwines the two projective-resolution comparisons. -/
@[reassoc (attr := simp)]
theorem inv_fac {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    (homotopyComparisonIso P Q).inv ≫
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map P.π =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).map Q.π := sorry

/-- The canonical comparison from a projective resolution to itself is the identity isomorphism. -/
@[simp]
theorem refl {K : CochainComplex 𝒜 ℤ} (P : ProjectiveResolution K) :
    homotopyComparisonIso P P = Iso.refl _ := sorry

/-- Reversing the canonical comparison exchanges its two projective resolutions. -/
@[simp]
theorem symm {K : CochainComplex 𝒜 ℤ} (P Q : ProjectiveResolution K) :
    (homotopyComparisonIso P Q).symm = homotopyComparisonIso Q P := sorry

/-- Canonical comparisons compose transitively through an intermediate projective resolution. -/
@[simp]
theorem trans {K : CochainComplex 𝒜 ℤ} (P Q R : ProjectiveResolution K) :
    homotopyComparisonIso P Q ≪≫ homotopyComparisonIso Q R =
      homotopyComparisonIso P R := sorry

end homotopyComparisonIso

/-- A morphism is a homotopy comparison exactly when it is the forward map of the canonical
comparison isomorphism. -/
@[simp]
theorem isHomotopyComparison_iff {K : CochainComplex 𝒜 ℤ}
    (P Q : ProjectiveResolution K)
    (a : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P.complex ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj Q.complex) :
    P.IsHomotopyComparison Q a ↔ a = (homotopyComparisonIso P Q).hom := sorry

/-- Canonical homotopy maps are natural under changing the chosen projective resolutions of their
source and target complexes. -/
@[reassoc, stacks 0648 "chosen-model naturality of projective-resolution homotopy maps"]
theorem homotopyMap_naturality {K L : CochainComplex 𝒜 ℤ}
    (P P' : ProjectiveResolution K) (Q Q' : ProjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyComparisonIso P P').hom ≫ P'.homotopyMap Q' u =
      P.homotopyMap Q u ≫ (homotopyComparisonIso Q Q').hom := sorry

/-- Changing only the source projective resolution acts by precomposition with the canonical
comparison isomorphism. -/
@[reassoc (attr := simp)]
theorem homotopyMap_changeSource {K L : CochainComplex 𝒜 ℤ}
    (P P' : ProjectiveResolution K) (Q : ProjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    (homotopyComparisonIso P P').hom ≫ P'.homotopyMap Q u =
      P.homotopyMap Q u := sorry

/-- Changing only the target projective resolution acts by postcomposition with the canonical
comparison isomorphism. -/
@[reassoc (attr := simp)]
theorem homotopyMap_changeTarget {K L : CochainComplex 𝒜 ℤ}
    (P : ProjectiveResolution K) (Q Q' : ProjectiveResolution L)
    (u : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ⟶
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) :
    P.homotopyMap Q u ≫ (homotopyComparisonIso Q Q').hom =
      P.homotopyMap Q' u := sorry

end CochainComplex.ProjectiveResolution
