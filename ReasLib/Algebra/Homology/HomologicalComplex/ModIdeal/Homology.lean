module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Homology
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal

/-!
# Homology of a complex modulo an ideal

Restriction of scalars along `A ⟶ A ⧸ I` commutes with homology.  Consequently, an
`A`-linear morphism between homology objects of scalar-restricted quotient complexes has a unique
`A ⧸ I`-linear refinement.  This file exposes both comparisons without rebuilding quotient
module structures locally.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace HomologicalComplex.ModIdeal.Homology

variable {A : Type u} [CommRing A]
variable {ι : Type w} {c : ComplexShape ι}

/-- Homology of the scalar-restricted quotient complex is canonically the restriction of the
homology of the quotient-ring complex. -/
@[stacks 00DV "homology of a complex modulo an ideal"]
noncomputable def restrictedIso (I : Ideal A)
    (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    (restrictedComplex I K).homology i ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj ((complex I K).homology i) :=
  ModuleCat.restrictScalarsHomologyIso (Ideal.Quotient.mk I) (complex I K) i

/-- The restricted-homology comparison is natural in morphisms of complexes. -/
@[reassoc]
theorem restrictedIso_hom_naturality (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (φ : K ⟶ L) (i : ι) :
    HomologicalComplex.homologyMap (restrictedMap I φ) i ≫
        (restrictedIso I L i).hom =
      (restrictedIso I K i).hom ≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
          (HomologicalComplex.homologyMap (map I φ) i) := sorry

/-- Regard a quotient-ring-linear homology morphism as an `A`-linear morphism between the
homology objects of the scalar-restricted quotient complexes. -/
def restrict (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (i j : ι)
    (φ : (complex I K).homology i ⟶ (complex I L).homology j) :
    (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j :=
  (restrictedIso I K i).hom ≫
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map φ ≫
      (restrictedIso I L j).inv

/-- Recover the unique `A ⧸ I`-linear morphism underlying an `A`-linear morphism between
homology objects of scalar-restricted quotient complexes. -/
@[stacks 00DV "linear descent on homology modulo an ideal"]
def descend (I : Ideal A) (i j : ι)
    {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j) :
    (complex I K).homology i ⟶ (complex I L).homology j :=
  ModuleCat.RestrictScalars.Surjective.preimage
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    ((restrictedIso I K i).inv ≫ φ ≫ (restrictedIso I L j).hom)

/-- Restricting a descended homology morphism recovers the original `A`-linear morphism. -/
@[simp]
theorem restrict_descend (I : Ideal A) (i j : ι)
    {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j) :
    restrict I i j (descend I i j φ) = φ := sorry

/-- Descending a restricted quotient-ring homology morphism leaves it unchanged. -/
@[simp]
theorem descend_restrict (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (i j : ι)
    (φ : (complex I K).homology i ⟶ (complex I L).homology j) :
    descend I i j (restrict I i j φ) = φ := sorry

/-- The canonical equivalence between quotient-ring-linear homology morphisms and their
scalar-restricted `A`-linear views. -/
@[stacks 00DV "homology morphisms modulo an ideal"]
def homEquiv (I : Ideal A)
    (K L : HomologicalComplex (ModuleCat.{v} A) c) (i j : ι) :
    ((complex I K).homology i ⟶ (complex I L).homology j) ≃
      ((restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j) where
  toFun := restrict I i j
  invFun := descend I i j
  left_inv := descend_restrict I i j
  right_inv := restrict_descend I i j

/-- Characterization of descent after transporting both homology objects through the canonical
restriction-of-scalars comparisons. -/
theorem descend_spec (I : Ideal A) (i j : ι)
    {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j) :
    (restrictedIso I K i).hom ≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map
          (descend I i j φ) =
      φ ≫ (restrictedIso I L j).hom := sorry

/-- A quotient-ring-linear homology morphism satisfying the descent equation is uniquely the
canonical descent. -/
theorem descend_unique (I : Ideal A) (i j : ι)
    {K L : HomologicalComplex (ModuleCat.{v} A) c}
    (φ : (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j)
    (ψ : (complex I K).homology i ⟶ (complex I L).homology j)
    (hψ : (restrictedIso I K i).hom ≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map ψ =
      φ ≫ (restrictedIso I L j).hom) :
    ψ = descend I i j φ := sorry

/-- Scalar restriction preserves identity homology morphisms. -/
@[simp]
theorem restrict_id (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    restrict I i i (𝟙 ((complex I K).homology i)) =
      𝟙 ((restrictedComplex I K).homology i) := sorry

/-- Scalar restriction preserves composition of homology morphisms. -/
@[simp]
theorem restrict_comp (I : Ideal A)
    {K L M : HomologicalComplex (ModuleCat.{v} A) c} (i j k : ι)
    (φ : (complex I K).homology i ⟶ (complex I L).homology j)
    (ψ : (complex I L).homology j ⟶ (complex I M).homology k) :
    restrict I i k (φ ≫ ψ) = restrict I i j φ ≫ restrict I j k ψ := sorry

/-- Scalar restriction preserves zero homology morphisms. -/
@[simp]
theorem restrict_zero (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (i j : ι) :
    restrict I i j (0 : (complex I K).homology i ⟶ (complex I L).homology j) = 0 := sorry

/-- Scalar restriction preserves addition of homology morphisms. -/
theorem restrict_add (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (i j : ι)
    (φ ψ : (complex I K).homology i ⟶ (complex I L).homology j) :
    restrict I i j (φ + ψ) = restrict I i j φ + restrict I i j ψ := sorry

/-- Linear descent preserves identity homology morphisms. -/
@[simp]
theorem descend_id (I : Ideal A) (K : HomologicalComplex (ModuleCat.{v} A) c) (i : ι) :
    descend I i i (𝟙 ((restrictedComplex I K).homology i)) =
      𝟙 ((complex I K).homology i) := sorry

/-- Linear descent preserves composition of homology morphisms. -/
@[simp]
theorem descend_comp (I : Ideal A)
    {K L M : HomologicalComplex (ModuleCat.{v} A) c} (i j k : ι)
    (φ : (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j)
    (ψ : (restrictedComplex I L).homology j ⟶ (restrictedComplex I M).homology k) :
    descend I i k (φ ≫ ψ) = descend I i j φ ≫ descend I j k ψ := sorry

/-- Linear descent preserves zero homology morphisms. -/
@[simp]
theorem descend_zero (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (i j : ι) :
    descend I i j (0 : (restrictedComplex I K).homology i ⟶
      (restrictedComplex I L).homology j) = 0 := sorry

/-- Linear descent preserves addition of homology morphisms. -/
theorem descend_add (I : Ideal A)
    {K L : HomologicalComplex (ModuleCat.{v} A) c} (i j : ι)
    (φ ψ : (restrictedComplex I K).homology i ⟶ (restrictedComplex I L).homology j) :
    descend I i j (φ + ψ) = descend I i j φ + descend I i j ψ := sorry

end HomologicalComplex.ModIdeal.Homology
