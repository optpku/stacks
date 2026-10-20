module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Comparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafRestriction

/-!
# Inverse-image comparison of small étale sheaves

A morphism `φ : x ⟶ y` of a category fibred in groupoids, lying over
`a : U ⟶ V`, induces the inverse-image comparison
`a_small⁻¹(F|_{V_étale}) ⟶ F|_{U_étale}` as the sheaf-adjunction adjunct of
the existing pushforward comparison `comparisonPush`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {x y : X.total} (φ : x ⟶ y)
variable [HasWeakSheafify (X.p.obj x).left.smallEtaleTopology (Type (u + 1))]
variable [∀ P : (X.p.obj y).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (smallEtalePullback (X.p.map φ).left).op.HasLeftKanExtension P]

/-- Inverse-image comparison morphism
`a_small⁻¹(F|_{V_étale}) ⟶ F|_{U_étale}` associated to `φ : x ⟶ y`, the
adjunct of `comparisonPush φ F.obj`. -/
def comparison (F : Sheaf X.etaleTopology (Type (u + 1))) :
    ((smallEtalePullback (X.p.map φ).left).sheafPullback (Type (u + 1))
        (X.p.obj y).left.smallEtaleTopology
        (X.p.obj x).left.smallEtaleTopology).obj
      (restrictSmallEtaleSheaf F y) ⟶
    restrictSmallEtaleSheaf F x :=
  ((smallEtalePullback_sheafAdjunction (X.p.map φ).left (Type (u + 1))).homEquiv
      (restrictSmallEtaleSheaf F y) (restrictSmallEtaleSheaf F x)).symm
    (ObjectProperty.homMk (comparisonPush φ F.obj))

/-- `comparison` is the adjunct of the sheaf morphism whose underlying map is
`comparisonPush φ F.obj`. -/
theorem comparison_adjunct (F : Sheaf X.etaleTopology (Type (u + 1))) :
    comparison φ F =
      ((smallEtalePullback_sheafAdjunction (X.p.map φ).left (Type (u + 1))).homEquiv
          (restrictSmallEtaleSheaf F y) (restrictSmallEtaleSheaf F x)).symm
        (ObjectProperty.homMk (comparisonPush φ F.obj)) :=
  sorry

/-- The sheaf morphism corresponding to `comparison φ F` under the small étale
pullback adjunction has underlying presheaf map `comparisonPush φ F.obj`. -/
theorem comparison_hom (F : Sheaf X.etaleTopology (Type (u + 1))) :
    (((smallEtalePullback_sheafAdjunction (X.p.map φ).left (Type (u + 1))).homEquiv
          (restrictSmallEtaleSheaf F y) (restrictSmallEtaleSheaf F x))
        (comparison φ F)).hom =
      comparisonPush φ F.obj :=
  sorry

end AlgebraicGeometry.GroupoidsOver
