/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Lemma_63_3_10_Comparison

/-!
# Compactification of compactly supported global étale sections

Lemma 63.3.10: if `j : X ⟶ X̄` is an open immersion of schemes over a field
`k` with `X̄` proper over `k`, then `H^0_c(X, F) ≃+ H^0_c(X̄, j_! F)`, and
hence `H^0_c(X, F) ≃+ H^0(X̄, j_! F)`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k]
variable {X Xbar : SchemeOverField k} (j : X ⟶ Xbar)
variable [IsOpenImmersion j.left] [IsProper Xbar.hom]
variable [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j.left).op.HasLeftKanExtension F]
variable [HasWeakSheafify Xbar.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ P : Xbar.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback j.left).op.HasLeftKanExtension P]
variable [((smallEtalePullback j.left).sheafPushforwardContinuous AddCommGrpCat.{u}
    Xbar.left.smallEtaleTopology X.left.smallEtaleTopology).IsRightAdjoint]

/-- Lemma 63.3.10 (1): Let `k` be a field. Let `j : X ⟶ X̄` be an open
immersion of schemes over `k` with `X̄` proper over `k`. For `F` in
`Ab(X_étale)` there is a canonical isomorphism
`H^0_c(X, F) ≃+ H^0_c(X̄, j_! F)`. -/
@[stacks 0F75]
def globalSectionsCompactSupportCompactifyEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportSubgroup X F ≃+
      globalSectionsCompactSupportSubgroup Xbar
        ((abelianExtensionByZero j.left).obj F) :=
  AddEquiv.ofBijective (globalSectionsCompactSupportCompactify j F)
    (globalSectionsCompactSupportCompactify_bijective j F)

/-- The underlying additive map of
`globalSectionsCompactSupportCompactifyEquiv` is the compactification
comparison. -/
theorem globalSectionsCompactSupportCompactifyEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X F) :
    globalSectionsCompactSupportCompactifyEquiv j F σ =
      globalSectionsCompactSupportCompactify j F σ :=
  sorry

/-- Lemma 63.3.10 (2): Let `k` be a field. Let `j : X ⟶ X̄` be an open
immersion of schemes over `k` with `X̄` proper over `k`. For `F` in
`Ab(X_étale)` the comparison of (1) together with
`H^0_c(X̄, j_! F) = H^0(X̄, j_! F)` from Lemma 63.3.8 yields a canonical
isomorphism `H^0_c(X, F) ≃+ H^0(X̄, j_! F)`. -/
@[stacks 0F75]
def globalSectionsCompactSupportCompactifyGlobalEquiv
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportSubgroup X F ≃+
      ((abelianExtensionByZero j.left).obj F).obj.obj
        (op (globalEtale Xbar.left)) :=
  (globalSectionsCompactSupportCompactifyEquiv j F).trans
    (AddEquiv.ofBijective
      (globalSectionsCompactSupportSubgroup Xbar
          ((abelianExtensionByZero j.left).obj F)).subtype
      (globalSectionsCompactSupportSubgroup_subtype_bijective
        ((abelianExtensionByZero j.left).obj F)))

/-- The underlying map of `globalSectionsCompactSupportCompactifyGlobalEquiv`
is the compactification comparison followed by the inclusion of compactly
supported sections into all global sections. -/
theorem globalSectionsCompactSupportCompactifyGlobalEquiv_apply
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X F) :
    globalSectionsCompactSupportCompactifyGlobalEquiv j F σ =
      (globalSectionsCompactSupportSubgroup Xbar
          ((abelianExtensionByZero j.left).obj F)).subtype
        (globalSectionsCompactSupportCompactify j F σ) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
