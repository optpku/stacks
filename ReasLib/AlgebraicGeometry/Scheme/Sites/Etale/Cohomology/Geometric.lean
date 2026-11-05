/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Abelian
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.PullbackIso

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- Restriction of an abelian small-étale sheaf to the geometric fibre, as inverse
image along `FieldExtension.toSource`. -/
abbrev geometricAbelianSheafRestriction (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
      AddCommGrpCat.{u} :=
  (etaleAbelianSheafPullback
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F

/-- Unfolding of `geometricAbelianSheafRestriction` as abelian small-étale inverse image along
the projection `X_k̄ ⟶ X`. -/
theorem geometricAbelianSheafRestriction_eq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    geometricAbelianSheafRestriction X F =
      (etaleAbelianSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F :=
  rfl

/-- Geometric étale cohomology `H^j(X_k̄, F|_{X_k̄})` of an abelian sheaf. -/
abbrev geometricEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    AddCommGrpCat.{u} :=
  (Sheaf.functorH
      (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology j).obj
    (geometricAbelianSheafRestriction X F)

/-- Unfolding of `geometricEtaleHq` as `Sheaf.functorH` of `geometricAbelianSheafRestriction`. -/
theorem geometricEtaleHq_eq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    geometricEtaleHq X F j =
      (Sheaf.functorH
          (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
          j).obj
        (geometricAbelianSheafRestriction X F) :=
  rfl

variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Pasting isomorphism identifying `(Spec(σ) × id_X)^{-1}(F|_{X_k̄})` with
`F|_{X_k̄}`, using that Galois base change lies over `X`. -/
def galoisSheafPastingIso (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : Gal(AlgebraicClosure k / k)) :
    (etaleAbelianSheafPullback
        (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).obj
      (geometricAbelianSheafRestriction X F) ≅ geometricAbelianSheafRestriction X F :=
  (etaleAbelianSheafPullback_comp
        (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
        (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app F ≪≫
    (eqToIso (congrArg (fun r ↦ etaleAbelianSheafPullback r)
          (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ))).app F

/-- Unfolding of `galoisSheafPastingIso` as composite-then-congruence of inverse
images along the commuting triangle for `FieldExtension.Galois.map`. -/
theorem galoisSheafPastingIso_spec (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : Gal(AlgebraicClosure k / k)) :
    galoisSheafPastingIso X F σ =
      (etaleAbelianSheafPullback_comp
            (FieldExtension.toSource k (AlgebraicClosure k) X.hom)
            (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)).app F ≪≫
        (eqToIso (congrArg (fun r ↦ etaleAbelianSheafPullback r)
          (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) X.hom σ))).app F :=
  rfl

/-- The Galois action of `σ` on `H^j(X_k̄, F|_{X_k̄})`, sending `ξ` to
`(Spec(σ) × id_X)^* ξ`. -/
def galoisEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ)
    (σ : Gal(AlgebraicClosure k / k)) :
    geometricEtaleHq X F j ⟶ geometricEtaleHq X F j :=
  etaleHq_pullback (FieldExtension.Galois.map k (AlgebraicClosure k) X.hom σ)
      (geometricAbelianSheafRestriction X F) j ≫
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
          (geometricAbelianSheafRestriction X F) j ≫
        (Sheaf.functorH
            (FieldExtension.baseChange k (AlgebraicClosure k)
              X.hom).smallEtaleTopology
            j).map
          (galoisSheafPastingIso X F σ).hom :=
  rfl

end AlgebraicGeometry.SchemeOverField
