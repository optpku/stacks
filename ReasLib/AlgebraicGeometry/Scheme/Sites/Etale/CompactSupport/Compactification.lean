module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CompactSupport.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.OpenImmersion

/-!
# Compactification of compactly supported global étale sections

For an open immersion into a scheme proper over a field, extension by zero
identifies compactly supported global sections with global sections on the
proper target.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
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
      (@CategoryTheory.asIso _ _ _ _
        ((abelianExtensionByZero_adjunction j.left).unit.app F)
        (abelianExtensionByZero_unit_isIso_of_isOpenImmersion j.left F)))

/-- The compactification comparison is covariance along `j` after transport
along the restriction identification `(j_! F)|_X ≅ F`. -/
theorem globalSectionsCompactSupportCompactify_comp
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) :
    globalSectionsCompactSupportCompactify j F =
      (globalSectionsCompactSupportOpenImmersion j
          ((abelianExtensionByZero j.left).obj F)).comp
        (globalSectionsCompactSupportMapIso X
          (@CategoryTheory.asIso _ _ _ _
        ((abelianExtensionByZero_adjunction j.left).unit.app F)
        (abelianExtensionByZero_unit_isIso_of_isOpenImmersion j.left F))) :=
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
          (@CategoryTheory.asIso _ _ _ _
        ((abelianExtensionByZero_adjunction j.left).unit.app F)
        (abelianExtensionByZero_unit_isIso_of_isOpenImmersion j.left F)) σ) :=
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

/-- Extension by zero along an open immersion into a proper scheme induces a
canonical additive equivalence on compactly supported global étale sections. -/
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

/-- Extension by zero along an open immersion into a proper scheme identifies
compactly supported global étale sections on the source with all global
sections on the target. -/
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
