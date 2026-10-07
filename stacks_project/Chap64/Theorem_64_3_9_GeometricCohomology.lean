module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap59.Lemma_59_80_9_Pullback

/-!
# Geometric étale cohomology of an abelian sheaf

This leaf owns restriction of an abelian small-étale sheaf to the geometric
fibre `X_k̄` and the corresponding cohomology objects `H^j(X_k̄, F|_{X_k̄})`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

/-- Inverse-image identification along equal morphisms, by substitution of the
morphism equality. -/
def etaleAbelianSheafPullback_congr {A B : Scheme.{u}} {p q : A ⟶ B} (h : p = q) :
    etaleAbelianSheafPullback p ≅ etaleAbelianSheafPullback q :=
  eqToIso (congrArg (fun r : A ⟶ B ↦ etaleAbelianSheafPullback r) h)

/-- Unfolding of `etaleAbelianSheafPullback_congr` as `eqToIso` of the substituted
pullback functor. -/
theorem etaleAbelianSheafPullback_congr_eq {A B : Scheme.{u}} {p q : A ⟶ B}
    (h : p = q) :
    etaleAbelianSheafPullback_congr h =
      eqToIso (congrArg (fun r : A ⟶ B ↦ etaleAbelianSheafPullback r) h) :=
  sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- Restriction of an abelian small-étale sheaf to the geometric fibre, as inverse
image along `FieldExtension.toSource`. -/
abbrev geometricRestriction (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Sheaf (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
      AddCommGrpCat.{u} :=
  (etaleAbelianSheafPullback
      (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F

/-- Unfolding of `geometricRestriction` as abelian small-étale inverse image along
the projection `X_k̄ ⟶ X`. -/
theorem geometricRestriction_eq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    geometricRestriction X F =
      (etaleAbelianSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) X.hom)).obj F :=
  sorry

/-- Geometric étale cohomology `H^j(X_k̄, F|_{X_k̄})` of an abelian sheaf. -/
abbrev geometricEtaleHq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    AddCommGrpCat.{u} :=
  (Sheaf.functorH
      (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology j).obj
    (geometricRestriction X F)

/-- Unfolding of `geometricEtaleHq` as `Sheaf.functorH` of `geometricRestriction`. -/
theorem geometricEtaleHq_eq (X : SchemeOverField k)
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) (j : ℕ) :
    geometricEtaleHq X F j =
      (Sheaf.functorH
          (FieldExtension.baseChange k (AlgebraicClosure k) X.hom).smallEtaleTopology
          j).obj
        (geometricRestriction X F) :=
  sorry

end AlgebraicGeometry.SchemeOverField
