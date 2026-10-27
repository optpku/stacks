/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.RingTheory.Extension.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import ReasLib.RingTheory.CotangentComplex.NaiveComparison
public import ReasLib.RingTheory.CotangentComplex.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent homology of a surjective ring map

For a surjective homomorphism of commutative rings, the cotangent complex has
vanishing degree-zero homology and degree-minus-one homology canonically identified
with the conormal module of its kernel. The comparison is induced by the empty
polynomial presentation. Quotient algebras specialize this module to `I/I²`.
These constructions use commutative algebras in one universe; extension to ringed
sites requires additional derived-functor infrastructure.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open Algebra
open Algebra.NaiveCotangent
open CommRingCat.Under.CotangentComplex
open CommRingCat.Under.FreeAlgebra
open DerivedCategory.TStructure
open DerivedCategory.TruncGE

universe u

noncomputable section

namespace Algebra.CotangentComplex

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The degree-zero homology of the cotangent complex of a surjective algebra map vanishes. -/
@[stacks 08RA]
theorem homology_zero_isZero_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    IsZero ((Algebra.cotangentComplex A B).homology 0) :=
  sorry

/-- The structure map `A ⟶ A[∅]` of the empty polynomial presentation is an isomorphism. -/
instance ofBaseSource_isIso :
    IsIso ((functor (CommRingCat.of A)).obj PEmpty.{u + 1}).hom :=
  sorry

/-- Kernel of `A[∅] ⟶ B` is contained in the comap of `ker(A ⟶ B)` along the inverse of
`A ⟶ A[∅]`. -/
theorem ofBase_ker_le_comap :
    RingHom.ker (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom ≤
      (RingHom.ker (algebraMap A B)).comap
        (RingHom.toIntAlgHom
          (inv ((functor (CommRingCat.of A)).obj PEmpty.{u + 1}).hom).hom) :=
  sorry

/-- The `P`-linear map from `J/J²` of `A[∅] ⟶ B` to restricted-scalar `I/I²`. -/
def ofBaseHom_kerCotangentToRestrict
    (h : Function.Surjective (algebraMap A B)) :
    naiveConormalRestrict (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶
      (ModuleCat.restrictScalars
          (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).obj
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent) :=
  ConcreteCategory.ofHom
    { toFun := fun x ↦
        Ideal.mapCotangent
          (RingHom.ker (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
          (RingHom.ker (algebraMap A B))
          (RingHom.toIntAlgHom
            (inv ((functor (CommRingCat.of A)).obj PEmpty.{u + 1}).hom).hom)
          ofBase_ker_le_comap x
      map_add' := sorry
      map_smul' := sorry }

/-- `ofBaseHom_kerCotangentToRestrict` is `Ideal.mapCotangent` along the inverse of
`A ⟶ A[∅]`. -/
theorem ofBaseHom_kerCotangentToRestrict_apply
    (h : Function.Surjective (algebraMap A B))
    (x : naiveConormalRestrict (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) :
    ofBaseHom_kerCotangentToRestrict h x =
      Ideal.mapCotangent
        (RingHom.ker (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom)
        (RingHom.ker (algebraMap A B))
        (RingHom.toIntAlgHom
          (inv ((functor (CommRingCat.of A)).obj PEmpty.{u + 1}).hom).hom)
        ofBase_ker_le_comap x :=
  sorry

/-- The `B`-module map from the naive conormal of `(A ⟶ B)` to `I/I²`. -/
def ofBaseHom_conormalToCotangent
    (h : Function.Surjective (algebraMap A B)) :
    naiveConormal (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶
      ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent :=
  ((ModuleCat.extendRestrictScalarsAdj
        (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).homEquiv _ _).symm
    (ofBaseHom_kerCotangentToRestrict h)

/-- Unfolding of `ofBaseHom_conormalToCotangent` through the extension-restriction adjunction. -/
theorem ofBaseHom_conormalToCotangent_eq
    (h : Function.Surjective (algebraMap A B)) :
    ofBaseHom_conormalToCotangent h =
      ((ModuleCat.extendRestrictScalarsAdj
          (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))).right.hom).homEquiv _ _).symm
        (ofBaseHom_kerCotangentToRestrict h) :=
  sorry

/-- The degree `-1` component of the map from the naive complex of `(A ⟶ B)` to
`I/I²` placed in cohomological degree `-1`. -/
def ofBaseHom_toCotangent_f
    (h : Function.Surjective (algebraMap A B)) :
    (naiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).X (-1) ⟶
      ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent :=
  (naiveComplex_X_negOne (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).hom ≫
    ofBaseHom_conormalToCotangent h

/-- Incoming differentials of the naive complex of `(A ⟶ B)` vanish after
`ofBaseHom_toCotangent_f`. -/
theorem ofBaseHom_toCotangent_f_comp
    (h : Function.Surjective (algebraMap A B))
    (i : ℤ) (hi : (ComplexShape.up ℤ).Rel i (-1)) :
    (naiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))).d i (-1) ≫ ofBaseHom_toCotangent_f h = 0 :=
  sorry

/-- The naive complex of `(A ⟶ B)` mapping to the conormal module in degree `-1`. -/
def ofBaseHom_toCotangent
    (h : Function.Surjective (algebraMap A B)) :
    naiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ⟶
      (single (ModuleCat.{u} (CommRingCat.of B)) (ComplexShape.up ℤ) (-1)).obj
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent) :=
  mkHomToSingle (ofBaseHom_toCotangent_f h) (ofBaseHom_toCotangent_f_comp h)

/-- For a surjection, `ofBaseHom_toCotangent` is a quasi-isomorphism in degree `-1`. -/
instance ofBaseHom_toCotangent_quasiIsoAt
    (h : Function.Surjective (algebraMap A B)) :
    QuasiIsoAt (ofBaseHom_toCotangent h) (-1) :=
  sorry

/-- Identification of `H^{-1}` of the naive complex of `(A ⟶ B)` with `I/I²`. -/
def naiveComplex_ofBaseHom_homology_negOne_iso
    (h : Function.Surjective (algebraMap A B)) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of B)) (-1)).obj
      (DerivedCategory.Q.obj (naiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))))) ≅
      ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CommRingCat.of B)) (-1)).app
      (naiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) ≪≫
    isoOfQuasiIsoAt (ofBaseHom_toCotangent h) (-1) ≪≫
    singleObjHomologySelfIso (ComplexShape.up ℤ) (-1)
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent)

/-- The forward morphism of `naiveComplex_ofBaseHom_homology_negOne_iso` factors through
`homologyFunctorFactors` and `ofBaseHom_toCotangent`. -/
theorem naiveComplex_ofBaseHom_homology_negOne_iso_hom
    (h : Function.Surjective (algebraMap A B)) :
    (naiveComplex_ofBaseHom_homology_negOne_iso h).hom =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CommRingCat.of B)) (-1)).hom.app
          (naiveComplex (CommRingCat.of A)
      (Under.mk (CommRingCat.ofHom (algebraMap A B))) PEmpty.{u + 1}
      (ofBaseHom (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B))))) ≫
        homologyMap (ofBaseHom_toCotangent h) (-1) ≫
          (singleObjHomologySelfIso (ComplexShape.up ℤ) (-1)
            (ModuleCat.of B
              (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent)).hom :=
  sorry

/-- Identification of `H^{-1}` of `τ_{≥ -1} L_{B/A}` with `H^{-1}(L_{B/A})`. -/
def truncGE_homology_negOne_iso :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of B)) (-1)).obj
      ((t.truncGE (-1)).obj
        (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)))) ≅
    (Algebra.cotangentComplex A B).homology (-1) :=
  homologyIso
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)) (-1) (-1) le_rfl ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CommRingCat.of B)) (-1)).app
      (Algebra.cotangentComplex A B)

/-- The inverse of `truncGE_homology_negOne_iso` is homology of `truncGEπ` followed by
`homologyFunctorFactors`. -/
theorem truncGE_homology_negOne_iso_inv :
    truncGE_homology_negOne_iso.inv =
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} (CommRingCat.of B)) (-1)).inv.app
          (Algebra.cotangentComplex A B) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of B)) (-1)).map
          ((t.truncGEπ (-1)).app
            (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))) :=
  sorry

/-- The comparison morphism `I/I² ⟶ H^{-1}(L_{B/A})` induced by `toTruncGE_ofBase`
for the object `(A ⟶ B)` of `C_{B/A}`. -/
def homology_negOne_conormal_comparison
    (h : Function.Surjective (algebraMap A B)) :
    ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent ⟶
      (Algebra.cotangentComplex A B).homology (-1) :=
  (naiveComplex_ofBaseHom_homology_negOne_iso h).inv ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of B)) (-1)).map
      (toTruncGE_ofBase (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ≫
    truncGE_homology_negOne_iso.hom

/-- Unfolding of `homology_negOne_conormal_comparison` as the composite of the naive
conormal identification, `toTruncGE_ofBase`, and the truncated homology identification. -/
theorem homology_negOne_conormal_comparison_eq
    (h : Function.Surjective (algebraMap A B)) :
    homology_negOne_conormal_comparison h =
      (naiveComplex_ofBaseHom_homology_negOne_iso h).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (CommRingCat.of B)) (-1)).map
          (toTruncGE_ofBase (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))) ≫
        truncGE_homology_negOne_iso.hom :=
  sorry

/-- For a surjective algebra map with kernel `I`, the canonical comparison
`I/I² ⟶ H^{-1}(L_{B/A})` induced by the empty polynomial presentation is an isomorphism. -/
@[stacks 08RA]
theorem homology_negOne_iso_of_surjective
    (h : Function.Surjective (algebraMap A B)) :
    IsIso (homology_negOne_conormal_comparison h) :=
  sorry

end

/-- The quotient map `A ⟶ A ⧸ I` is surjective. -/
theorem algebraMap_quotient_surjective {A : Type u} [CommRing A] (I : Ideal A) :
    Function.Surjective (algebraMap A (A ⧸ I)) :=
  sorry

/-- The kernel of `algebraMap A (A ⧸ I)` is `I`. -/
theorem ker_algebraMap_quotient {A : Type u} [CommRing A] (I : Ideal A) :
    RingHom.ker (algebraMap A (A ⧸ I)) = I :=
  sorry

/-- Specialization of the degree-zero vanishing to a quotient algebra `A ⧸ I`. -/
theorem quotient_homology_zero_isZero {A : Type u} [CommRing A] (I : Ideal A) :
    IsZero ((Algebra.cotangentComplex A (A ⧸ I)).homology 0) :=
  sorry

/-- Transport of `Extension.ofSurjective.Cotangent` to `I.Cotangent` for a quotient algebra. -/
def quotient_conormalIso {A : Type u} [CommRing A] (I : Ideal A) :
    ModuleCat.of (A ⧸ I)
      (Extension.ofSurjective (Algebra.ofId A (A ⧸ I))
        (algebraMap_quotient_surjective I)).Cotangent ≅
    ModuleCat.of (A ⧸ I) I.Cotangent where
  hom :=
    ModuleCat.ofHom
      { toFun := fun x ↦
          (Ideal.Cotangent.equivOfEq _ _ (ker_algebraMap_quotient I))
            (Extension.Cotangent.val x)
        map_add' := sorry
        map_smul' := sorry }
  inv :=
    ModuleCat.ofHom
      { toFun := fun x ↦
          Extension.Cotangent.of
            ((Ideal.Cotangent.equivOfEq _ _ (ker_algebraMap_quotient I)).symm x)
        map_add' := sorry
        map_smul' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `quotient_conormalIso` applies `Ideal.Cotangent.equivOfEq` of
`ker_algebraMap_quotient`. -/
theorem quotient_conormalIso_apply {A : Type u} [CommRing A] (I : Ideal A)
    (x : (Extension.ofSurjective (Algebra.ofId A (A ⧸ I))
      (algebraMap_quotient_surjective I)).Cotangent) :
    (quotient_conormalIso I).hom x =
      (Ideal.Cotangent.equivOfEq _ _ (ker_algebraMap_quotient I))
        (Extension.Cotangent.val x) :=
  sorry

/-- Specialization of the conormal comparison of a surjection to a quotient algebra `A ⧸ I`. -/
def quotient_homology_negOne_conormal_comparison {A : Type u} [CommRing A] (I : Ideal A) :
    ModuleCat.of (A ⧸ I) I.Cotangent ⟶
      (Algebra.cotangentComplex A (A ⧸ I)).homology (-1) :=
  (quotient_conormalIso I).inv ≫
    homology_negOne_conormal_comparison (algebraMap_quotient_surjective I)

/-- The quotient conormal comparison is an isomorphism. -/
theorem quotient_homology_negOne_isIso {A : Type u} [CommRing A] (I : Ideal A) :
    IsIso (quotient_homology_negOne_conormal_comparison I) :=
  sorry

end Algebra.CotangentComplex
