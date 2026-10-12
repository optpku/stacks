/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.QuotientByIdeal.Mapped

@[expose] public section

/-!
# Quotienting an algebra map by an ideal of the base

This file supplies the map induced by an algebra homomorphism after extending
one ideal of the base ring.  The quotient algebra and scalar-tower instances
are the canonical instances from `Mathlib.RingTheory.Ideal.Over`.
-/

universe u v w

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

namespace BaseIdeal

/-- An `R`-algebra homomorphism carries the extension of a base ideal in its
source into the corresponding extension in its target.  This is generic
functoriality rather than a source-labelled theorem. -/
theorem map_le_comap (f : A →ₐ[R] B) (I : Ideal R) :
    Ideal.map (algebraMap R A) I ≤
      Ideal.comap f.toRingHom (Ideal.map (algebraMap R B) I) := sorry

/-- Tag `07F8`: the underlying ring homomorphism obtained by quotienting an
algebra map by the extensions of one base ideal. -/
@[stacks 07F8 "base-ideal quotient ring hom"]
def quotientRingHom (f : A →ₐ[R] B) (I : Ideal R) :
    (A ⧸ Ideal.map (algebraMap R A) I) →+*
      (B ⧸ Ideal.map (algebraMap R B) I) :=
  Ideal.quotientMap _ f.toRingHom (map_le_comap f I)

/-- Tag `07F8`: the canonical `R`-algebra map obtained by quotienting an algebra map by the
extensions of one base ideal.  Unlike `AlgHom.quotientByBaseIdeal`, this keeps the original base
ring as scalars, which is the appropriate interface for `R`-linear quotient constructions. -/
@[stacks 07F8 "base-ideal quotient algebra map over the original base"]
def quotientMap (f : A →ₐ[R] B) (I : Ideal R) :
    (A ⧸ Ideal.map (algebraMap R A) I) →ₐ[R]
      (B ⧸ Ideal.map (algebraMap R B) I) :=
  Ideal.quotientMapₐ
    (Ideal.map (algebraMap R B) I) f (map_le_comap f I)

/-- Tag `07F8`: the base-ideal quotient map sends a residue class to the residue class of its
image. -/
@[simp, stacks 07F8 "base-ideal quotient algebra map on representatives"]
theorem quotientMap_apply_mk (f : A →ₐ[R] B) (I : Ideal R) (x : A) :
    quotientMap f I
        (Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R B) I) (f x) := sorry

/-- Tag `07F8`: forgetting the `R`-algebra structure on `quotientMap` recovers the canonical
base-ideal quotient ring homomorphism. -/
@[simp, stacks 07F8 "base-ideal quotient map ring-hom bridge"]
theorem quotientMap_toRingHom (f : A →ₐ[R] B) (I : Ideal R) :
    (quotientMap f I).toRingHom = quotientRingHom f I := sorry

/-- Tag `07F8`: the quotient map induced by an `R`-algebra homomorphism commutes with the
canonical comparisons between source-ideal and extended-ideal module quotients. -/
@[stacks 07F8 "base-ideal quotient comparison naturality"]
theorem idealQuotientEquiv_naturality (f : A →ₐ[R] B) (I : Ideal R) :
    (Ideal.Quotient.Map.idealQuotientEquiv (R := R) (S := B) I).toLinearMap ∘ₗ
          f.toLinearMap.quotientMapByIdeal I =
      (quotientMap f I).toLinearMap ∘ₗ
        (Ideal.Quotient.Map.idealQuotientEquiv (R := R) (S := A) I).toLinearMap := sorry

/-- Tag `07F8`: quotienting by a base ideal carries the image of any source submonoid to the
image of its image under the original algebra map.  This is the localization-facing form of the
base-ideal quotient map. -/
@[stacks 07F8 "base-ideal quotient map on submonoids"]
theorem quotientMap_map_algebraMapSubmonoid
    (f : A →ₐ[R] B) (I : Ideal R) (M : Submonoid A) :
    Submonoid.map (quotientMap f I).toMonoidHom
        (Algebra.algebraMapSubmonoid (A ⧸ Ideal.map (algebraMap R A) I) M) =
      Algebra.algebraMapSubmonoid (B ⧸ Ideal.map (algebraMap R B) I)
        (Submonoid.map (f : A →+* B) M) := sorry

/-- Tag `07F8`: the quotient ring homomorphism commutes with the canonical maps
from `R / I`. -/
@[simp, stacks 07F8 "base-ideal quotient scalar bridge"]
theorem quotientRingHom_commutes (f : A →ₐ[R] B)
    (I : Ideal R) (x : R ⧸ I) :
    quotientRingHom f I
        (algebraMap (R ⧸ I) (A ⧸ Ideal.map (algebraMap R A) I) x) =
      algebraMap (R ⧸ I) (B ⧸ Ideal.map (algebraMap R B) I) x := sorry

end BaseIdeal

/-- Tag `07F8`: the algebra homomorphism induced after quotienting source and
target by the extensions of a single ideal of the base ring. -/
@[stacks 07F8 "base-ideal quotient map"]
def quotientByBaseIdeal (f : A →ₐ[R] B) (I : Ideal R) :
    (A ⧸ Ideal.map (algebraMap R A) I) →ₐ[R ⧸ I]
      (B ⧸ Ideal.map (algebraMap R B) I) where
  __ := BaseIdeal.quotientRingHom f I
  commutes' := BaseIdeal.quotientRingHom_commutes f I

/-- Tag `07F8`: the `R / I`-algebra view of a base-ideal quotient has the same underlying ring map
as the original-base view. -/
@[simp, stacks 07F8 "base-ideal quotient scalar-view bridge"]
theorem quotientByBaseIdeal_toRingHom (f : A →ₐ[R] B) (I : Ideal R) :
    (quotientByBaseIdeal f I).toRingHom = (BaseIdeal.quotientMap f I).toRingHom := sorry

namespace BaseIdeal

/-- Tag `07F8`: the original-base and quotient-base views of a base-ideal map
have the same surjectivity behavior. -/
@[stacks 07F8 "surjectivity bridge for base-ideal quotient maps"]
theorem quotientMap_surjective_iff (f : A →ₐ[R] B) (I : Ideal R) :
    Function.Surjective (quotientMap f I) ↔
      Function.Surjective (f.quotientByBaseIdeal I) := sorry

/-- Tag `07F8`: the original-base and quotient-base views of a base-ideal map
have the same bijectivity behavior. -/
@[stacks 07F8 "bijectivity bridge for base-ideal quotient maps"]
theorem quotientMap_bijective_iff (f : A →ₐ[R] B) (I : Ideal R) :
    Function.Bijective (quotientMap f I) ↔
      Function.Bijective (f.quotientByBaseIdeal I) := sorry

/-- Tag `07RD`: surjectivity of the canonical quotient algebra map is
equivalent to surjectivity of the original algebra map followed by the target
quotient projection. -/
@[stacks 07RD "surjectivity of a base-ideal quotient map"]
theorem quotient_surjective_iff (f : A →ₐ[R] B) (I : Ideal R) :
    Function.Surjective (f.quotientByBaseIdeal I) ↔
      Function.Surjective
        ((Ideal.Quotient.mkₐ R (I.map (algebraMap R B))).comp f) := sorry

end BaseIdeal

/-- Tag `07F8`: the quotient of an algebra map sends a residue class to the
residue class of its image. -/
@[simp, stacks 07F8 "base-ideal quotient generator"]
theorem quotientByBaseIdeal_mk (f : A →ₐ[R] B) (I : Ideal R) (x : A) :
    quotientByBaseIdeal f I
        (Ideal.Quotient.mk (Ideal.map (algebraMap R A) I) x) =
      Ideal.Quotient.mk (Ideal.map (algebraMap R B) I) (f x) := sorry

/-- Tag `07F8`: quotienting an algebra map commutes with the two quotient maps. -/
@[stacks 07F8 "base-ideal quotient naturality"]
theorem quotientByBaseIdeal_comp_quotientMk (f : A →ₐ[R] B) (I : Ideal R) :
    (quotientByBaseIdeal f I).toRingHom.comp
        (Ideal.Quotient.mk (Ideal.map (algebraMap R A) I)) =
      (Ideal.Quotient.mk (Ideal.map (algebraMap R B) I)).comp f.toRingHom := sorry

end AlgHom
