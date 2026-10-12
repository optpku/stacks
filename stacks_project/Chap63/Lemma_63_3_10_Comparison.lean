/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import stacks_project.Chap59.Lemma_59_70_4
public import stacks_project.Chap63.Lemma_63_3_8
public import stacks_project.Chap63.Remark_63_3_9_Open_embeddings_and_compactly_supported_sections_OpenImmersion

/-!
# Compactification comparison for compactly supported global étale sections

If `j : X ⟶ X̄` is an open immersion of `k`-schemes and `X̄` is proper over
`k`, the adjunction unit `F ⟶ (j_! F)|_X` together with covariance of
`H^0_c` along `j` supplies a canonical comparison
`H^0_c(X, F) →+ H^0_c(X̄, j_! F)`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The inclusion of compactly supported global étale sections into all global
sections is bijective when the scheme is proper over the base field. -/
theorem globalSectionsCompactSupportSubgroup_subtype_bijective
    {k : Type u} [Field k] {X : SchemeOverField k} [IsProper X.hom]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (globalSectionsCompactSupportSubgroup X F).subtype :=
  sorry

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

/-- The adjunction unit `F ⟶ (j_! F)|_X` as an isomorphism of abelian
small-étale sheaves, for an open immersion `j`. -/
def abelianExtensionByZero_unitIso_of_isOpenImmersion
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    F ≅ (etaleRestrictionSheaf j.left AddCommGrpCat.{u}).obj
      ((abelianExtensionByZero j.left).obj F) :=
  @asIso _ _ _ _
    ((abelianExtensionByZero_adjunction j.left).unit.app F)
    (abelianExtensionByZero_unit_isIso_of_isOpenImmersion j.left F)

/-- The forward map of `abelianExtensionByZero_unitIso_of_isOpenImmersion` is the
extension-by-zero adjunction unit. -/
theorem abelianExtensionByZero_unitIso_of_isOpenImmersion_hom
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    (abelianExtensionByZero_unitIso_of_isOpenImmersion j F).hom =
      (abelianExtensionByZero_adjunction j.left).unit.app F :=
  sorry

/-- The canonical additive comparison `H^0_c(X, F) →+ H^0_c(X̄, j_! F)` obtained
by transporting along the restriction identification `(j_! F)|_X ≅ F` and then
applying covariance of compactly supported global sections along `j`. -/
def globalSectionsCompactSupportCompactify
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportSubgroup X F →+
      globalSectionsCompactSupportSubgroup Xbar
        ((abelianExtensionByZero j.left).obj F) :=
  (globalSectionsCompactSupportOpenImmersion j
      ((abelianExtensionByZero j.left).obj F)).comp
    (globalSectionsCompactSupportMapIso X
      (abelianExtensionByZero_unitIso_of_isOpenImmersion j F))

/-- The compactification comparison is covariance along `j` after transport
along the restriction identification `(j_! F)|_X ≅ F`. -/
theorem globalSectionsCompactSupportCompactify_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportCompactify j F =
      (globalSectionsCompactSupportOpenImmersion j
          ((abelianExtensionByZero j.left).obj F)).comp
        (globalSectionsCompactSupportMapIso X
          (abelianExtensionByZero_unitIso_of_isOpenImmersion j F)) :=
  sorry

/-- The compactification comparison acts by covariance on the transported
compactly supported section. -/
theorem globalSectionsCompactSupportCompactify_apply
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
    (σ : globalSectionsCompactSupportSubgroup X F) :
    globalSectionsCompactSupportCompactify j F σ =
      globalSectionsCompactSupportOpenImmersion j
          ((abelianExtensionByZero j.left).obj F)
        (globalSectionsCompactSupportMapIso X
          (abelianExtensionByZero_unitIso_of_isOpenImmersion j F) σ) :=
  sorry

/-- The compactification comparison `H^0_c(X, F) →+ H^0_c(X̄, j_! F)` is
injective. -/
theorem globalSectionsCompactSupportCompactify_injective
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Injective (globalSectionsCompactSupportCompactify j F) :=
  sorry

/-- The compactification comparison `H^0_c(X, F) →+ H^0_c(X̄, j_! F)` is
bijective. -/
theorem globalSectionsCompactSupportCompactify_bijective
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    Function.Bijective (globalSectionsCompactSupportCompactify j F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
