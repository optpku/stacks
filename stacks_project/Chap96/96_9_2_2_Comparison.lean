module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafComparison

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

variable (F : Sheaf X.etaleTopology (Type (u + 1)))

#check (AlgebraicGeometry.GroupoidsOver.comparison φ F :
    ((smallEtalePullback (X.p.map φ).left).sheafPullback (Type (u + 1))
        (X.p.obj y).left.smallEtaleTopology
        (X.p.obj x).left.smallEtaleTopology).obj
      (restrictSmallEtaleSheaf F y) ⟶
    restrictSmallEtaleSheaf F x)

#check (AlgebraicGeometry.GroupoidsOver.comparison_adjunct φ F :
    comparison φ F =
      ((smallEtalePullback_sheafAdjunction (X.p.map φ).left (Type (u + 1))).homEquiv
          (restrictSmallEtaleSheaf F y) (restrictSmallEtaleSheaf F x)).symm
        (ObjectProperty.homMk (comparisonPush φ F.obj)))

#check (AlgebraicGeometry.GroupoidsOver.comparison_hom φ F :
    (((smallEtalePullback_sheafAdjunction (X.p.map φ).left (Type (u + 1))).homEquiv
          (restrictSmallEtaleSheaf F y) (restrictSmallEtaleSheaf F x))
        (comparison φ F)).hom =
      comparisonPush φ F.obj)

end AlgebraicGeometry.GroupoidsOver
