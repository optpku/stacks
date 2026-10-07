module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_19_7_Point

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)

/-- Lemma 66.19.8 (1): the stalk functor on abelian étale presheaves is exact. -/
@[stacks 04K1]
theorem presheafAbelianStalkExact :
    exactFunctor _ _
      ((toSmallEtalePoint xbar).presheafFiber : _ ⥤ AddCommGrpCat.{u + 1}) :=
  sorry

/-- Lemma 66.19.8 (2): sheafification does not change the set-valued stalk at `xbar`. -/
@[stacks 04K1]
theorem sheafify_presheafFiber_iso (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    IsIso ((toSmallEtalePoint xbar).presheafFiber.map
      (toSheafify (smallEtaleTopology X) F)) :=
  sorry

/-- Lemma 66.19.8 (3): the stalk functor on abelian étale sheaves is exact. -/
@[stacks 04K1]
theorem sheafAbelianStalkExact :
    exactFunctor _ _
      ((toSmallEtalePoint xbar).sheafFiber : _ ⥤ AddCommGrpCat.{u + 1}) :=
  sorry

/-- Lemma 66.19.8 (4): the stalk functor on étale presheaves of sets is exact. -/
@[stacks 04K1]
theorem presheafTypeStalkExact :
    exactFunctor _ _
      ((toSmallEtalePoint xbar).presheafFiber : _ ⥤ Type (u + 1)) :=
  sorry

/-- Lemma 66.19.8 (5): the stalk functor on étale sheaves of sets is exact. -/
@[stacks 04K1]
theorem sheafTypeStalkExact :
    exactFunctor _ _
      ((toSmallEtalePoint xbar).sheafFiber : _ ⥤ Type (u + 1)) :=
  sorry

/-- Lemma 66.19.8 (6): the set-valued étale presheaf stalk functor preserves colimits. -/
@[stacks 04K1]
theorem presheafTypeStalkPreservesColimits :
    PreservesColimits
      ((toSmallEtalePoint xbar).presheafFiber : _ ⥤ Type (u + 1)) :=
  sorry

/-- Lemma 66.19.8 (7): the set-valued étale sheaf stalk functor preserves colimits. -/
@[stacks 04K1]
theorem sheafTypeStalkPreservesColimits :
    PreservesColimits
      ((toSmallEtalePoint xbar).sheafFiber : _ ⥤ Type (u + 1)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
