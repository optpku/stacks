module

public import stacks_project.Chap63.Lemma_63_3_11_Comparison

/-!
# Stalks of étale lower shriek as compactly supported fibre sections

Lemma 63.3.11: if `f : X ⟶ Y` is separated and locally of finite type and `F`
is an abelian sheaf on `X_étale`, then for every geometric point `ȳ` of `Y`
there is a canonical isomorphism `(f_! F)_ȳ ≅ H^0_c(X_ȳ, F|_{X_ȳ})`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
variable (ybar : GeometricPoint Y)

/-- Lemma 63.3.11: Let `f : X ⟶ Y` be a morphism of schemes which is separated
and locally of finite type. Let `F` be an abelian sheaf on `X_étale`. Then
there is a canonical isomorphism `(f_! F)_ȳ ⟶ H^0_c(X_ȳ, F|_{X_ȳ})` for any
geometric point `ȳ : Spec k ⟶ Y`. The geometric fibre `X_ȳ` is the chosen
pullback `ȳ ×_Y X`, and the map is given by pulling sections of `F` back to
this fibre. -/
@[stacks 0F76]
def etaleLowerShriekStalkCompactSupportIso
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((toSmallEtalePoint ybar).sheafFiber : _ ⥤ AddCommGrpCat.{u}).obj ((etaleLowerShriek f).obj F) ≅
      AddCommGrpCat.of
        (globalSectionsCompactSupportSubgroup (geometricFiberOverField f ybar)
          (abelianPullbackAlong (pullback.snd ybar.hom f) F)) :=
  asIso (etaleLowerShriekStalkToCompactSupport f ybar F)

/-- The forward map of `etaleLowerShriekStalkCompactSupportIso` is the
compact-support stalk comparison. -/
theorem etaleLowerShriekStalkCompactSupportIso_hom
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleLowerShriekStalkCompactSupportIso f ybar F).hom =
      etaleLowerShriekStalkToCompactSupport f ybar F :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
