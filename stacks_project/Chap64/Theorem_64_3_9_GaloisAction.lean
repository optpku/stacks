module

public import Mathlib.FieldTheory.Galois.Notation
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import stacks_project.Chap59.Lemma_59_91_6_BaseChange
public import stacks_project.Chap64.Lemma_64_3_2_Pullback
public import stacks_project.Chap64.Theorem_64_3_9_GeometricCohomology

/-!
# Galois action on geometric étale cohomology

This leaf owns the pasting isomorphism identifying inverse image along
`Spec(σ) × id_X` with restriction to `X_k̄`, and the induced endomorphism of
`H^j(X_k̄, F|_{X_k̄})`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Pasting isomorphism identifying `(Spec(σ) × id_X)^{-1}(F|_{X_k̄})` with
`F|_{X_k̄}`, using that Galois base change lies over `X`. -/
def galoisSheafPastingIso (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : Gal(AlgebraicClosure k / k)) :
    (etaleAbelianSheafPullback
        (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).obj
      (geometricRestriction X F) ≅ geometricRestriction X F :=
  (etaleAbelianSheafPullback_comp
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
        (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app F ≪≫
    (etaleAbelianSheafPullback_congr
        (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ)).app F

/-- Unfolding of `galoisSheafPastingIso` as composite-then-congruence of inverse
images along the commuting triangle for `FieldExtension.Galois.map`. -/
theorem galoisSheafPastingIso_spec (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : Gal(AlgebraicClosure k / k)) :
    galoisSheafPastingIso X F σ =
      (etaleAbelianSheafPullback_comp
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
            (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app F ≪≫
        (etaleAbelianSheafPullback_congr
            (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom
              σ)).app F :=
  sorry

/-- The Galois action of `σ` on `H^j(X_k̄, F|_{X_k̄})`, sending `ξ` to
`(Spec(σ) × id_X)^* ξ`. -/
def galoisEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ)
    (σ : Gal(AlgebraicClosure k / k)) :
    geometricEtaleHq X F j ⟶ geometricEtaleHq X F j :=
  etaleHq_pullback (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
      (geometricRestriction X F) j ≫
    (Sheaf.functorH
        (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
        j).map
      (galoisSheafPastingIso X F σ).hom

/-- Unfolding of `galoisEtaleHq` as cohomology pullback along `Spec(σ) × id_X`
followed by the coefficient identification from `galoisSheafPastingIso`. -/
theorem galoisEtaleHq_spec (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ)
    (σ : Gal(AlgebraicClosure k / k)) :
    galoisEtaleHq X F j σ =
      etaleHq_pullback (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
          (geometricRestriction X F) j ≫
        (Sheaf.functorH
            (FieldExtension.baseChange k (AlgebraicClosure k)
              X.hom).smallEtaleTopology
            j).map
          (galoisSheafPastingIso X F σ).hom :=
  sorry

end AlgebraicGeometry.SchemeOverField
