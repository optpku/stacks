module

public import ReasLib.CategoryTheory.Fibered.Groupoids.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Sites.SpecialCocontinuous
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Equivalences of associated fppf sheaf topoi

A local equivalence of categories fibred in groupoids over the big fppf site
induces an equivalence of their associated sheaf topoi.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)

/-- A local equivalence of categories fibred in groupoids over the big fppf
site is special cocontinuous for the associated fppf topologies. -/
theorem toFunctor_isSpecialCocontinuous
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (toFunctor f).IsSpecialCocontinuous X.fppfTopology Y.fppfTopology :=
  sorry

/-- A local equivalence of categories fibred in groupoids over the big fppf
site induces an equivalence through the inverse image of its canonical
morphism of associated fppf sheaf topoi. -/
theorem fppfMorphismOfTopoi_isEquivalence
    (hf : Hom.IsLocalEquivalence (Scheme.fppfTopology.over S) f) :
    (((toCartesianBasedFunctor f).morphismOfTopoiIn
        (Scheme.fppfTopology.over S)).inverseImage :
      Sheaf Y.fppfTopology (Type (u + 1)) ⥤
        Sheaf X.fppfTopology (Type (u + 1))).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
