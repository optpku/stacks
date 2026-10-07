module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homology and Exact Colimits

This file owns the shape-independent comparison between homology of a colimit
and the colimit of homology.  Resolution towers, filtrations, and telescopes
can use the same preservation instance and canonical comparison formulas.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe t w' w v u

namespace HomologicalComplex

section Comparison

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]
  [CategoryWithHomology A]
variable {ι : Type t} {c : ComplexShape ι}
variable {J : Type w} [Category.{w'} J]

/-- The canonical isomorphism from the colimit of homology objects to the
homology of a colimit, whenever the relevant homology functor preserves that
colimit. -/
noncomputable def homologyColimitIso (T : J ⥤ HomologicalComplex A c) (i : ι)
    [HasColimit T] [PreservesColimit T (homologyFunctor A c i)] :
    colimit (T ⋙ homologyFunctor A c i) ≅ (colimit T).homology i :=
  (preservesColimitIso (homologyFunctor A c i) T).symm

/-- The forward homology-colimit comparison sends every colimit leg to the
corresponding map on homology. -/
@[reassoc (attr := simp)]
theorem homologyColimitIso_hom_ι (T : J ⥤ HomologicalComplex A c) (i : ι)
    [HasColimit T] [PreservesColimit T (homologyFunctor A c i)] (j : J) :
    colimit.ι (T ⋙ homologyFunctor A c i) j ≫ (homologyColimitIso T i).hom =
      homologyMap (colimit.ι T j) i := sorry

/-- The inverse homology-colimit comparison sends the homology map induced by
a colimit leg back to the corresponding colimit-of-homology leg. -/
@[reassoc (attr := simp)]
theorem homologyColimitIso_inv_homologyMap_ι
    (T : J ⥤ HomologicalComplex A c) (i : ι)
    [HasColimit T] [PreservesColimit T (homologyFunctor A c i)] (j : J) :
    homologyMap (colimit.ι T j) i ≫ (homologyColimitIso T i).inv =
      colimit.ι (T ⋙ homologyFunctor A c i) j := sorry

/-- A cocone whose image under every homology functor is colimiting induces a
quasi-isomorphism from the chosen colimit, provided homology preserves that
colimit. -/
theorem quasiIso_colimitDesc_of_mapCocone_isColimit
    (T : J ⥤ HomologicalComplex A c) (s : Cocone T) [HasColimit T]
    [∀ i : ι, PreservesColimit T (homologyFunctor A c i)]
    (hs : ∀ i : ι, IsColimit ((homologyFunctor A c i).mapCocone s)) :
    QuasiIso (colimit.desc T s) := sorry

end Comparison

section Exact

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {ι : Type t} {c : ComplexShape ι}
variable {J : Type w} [Category.{w'} J]

/-- Homology preserves colimits of any shape for which colimits in the
ambient abelian category are exact. -/
@[stacks 0794]
noncomputable instance homologyFunctor_preservesColimitsOfShape_of_exact
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] (i : ι) :
    PreservesColimitsOfShape J (homologyFunctor A c i) := sorry

end Exact

end HomologicalComplex
