module

public import ReasLib.Algebra.Homology.ShortComplex.Colimits
public import ReasLib.Algebra.Homology.ShortComplex.DiagramHomology

/-!
# Homology and Exact Colimits of Short Complexes

This file owns the canonical comparison from a colimit of short-complex homology objects to the
homology of the colimit. It also exposes the comparison on cocone legs and the preservation
principles needed by arbitrary downstream diagram shapes.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type u'} [Category.{v'} J]

namespace ColimitHomology

/-- The canonical isomorphism from the colimit of the homology diagram to the homology of the
colimit of a diagram of short complexes. -/
noncomputable def iso (S : J ⥤ ShortComplex C) [HasColimit S]
    [PreservesColimit S (homologyFunctor C)] :
    colimit (S ⋙ homologyFunctor C) ≅ (colimit S).homology :=
  (preservesColimitIso (homologyFunctor C) S).symm

namespace iso

/-- The homology-colimit comparison sends each colimit leg to the homology map induced by the
corresponding short-complex colimit leg. -/
@[reassoc (attr := simp)]
theorem ι_hom (S : J ⥤ ShortComplex C) [HasColimit S]
    [PreservesColimit S (homologyFunctor C)] (j : J) :
    colimit.ι (S ⋙ homologyFunctor C) j ≫ (iso S).hom =
      homologyMap (colimit.ι S j) := sorry

/-- The inverse homology-colimit comparison sends the homology map of a colimit leg back to the
corresponding colimit-of-homology leg. -/
@[reassoc (attr := simp)]
theorem homologyMap_inv (S : J ⥤ ShortComplex C) [HasColimit S]
    [PreservesColimit S (homologyFunctor C)] (j : J) :
    homologyMap (colimit.ι S j) ≫ (iso S).inv =
      colimit.ι (S ⋙ homologyFunctor C) j := sorry

/-- The homology-colimit comparison is natural in the diagram of short complexes. -/
@[reassoc]
theorem naturality [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J (homologyFunctor C)]
    {S T : J ⥤ ShortComplex C} (f : S ⟶ T) :
    Limits.colim.map (Functor.whiskerRight f (homologyFunctor C)) ≫ (iso T).hom =
      (iso S).hom ≫ homologyMap (Limits.colim.map f) := sorry

end iso

/-- The actual homology comparison for an exact colimit, assembled from pointwise homology
and the native homology comparison of the supplied colimit functor. -/
noncomputable def exactIso [HasColimitsOfShape J C]
    [(Limits.colim (J := J) (C := C)).PreservesHomology]
    (S : J ⥤ ShortComplex C) :
    colimit (S ⋙ homologyFunctor C) ≅ (colimit S).homology :=
  (Limits.colim.mapIso (DiagramHomology.comparisonIso S)).symm ≪≫
    (((functorEquivalence J C).inverse.obj S).mapHomologyIso
      (Limits.colim (J := J) (C := C))).symm ≪≫
    (homologyFunctor C).mapIso (Colimit.iso S).symm

/-- The exact-colimit comparison carries every homology cocone leg to its actual homology map. -/
@[reassoc]
theorem ι_exactIso_hom [HasColimitsOfShape J C]
    [(Limits.colim (J := J) (C := C)).PreservesHomology]
    (S : J ⥤ ShortComplex C) (j : J) :
    colimit.ι (S ⋙ homologyFunctor C) j ≫ (exactIso S).hom =
      homologyMap (colimit.ι S j) := sorry

/-- The image homology cocone has an explicit descent using the actual reverse comparison. -/
noncomputable def isColimitHomologyCocone [HasColimitsOfShape J C]
    [(Limits.colim (J := J) (C := C)).PreservesHomology]
    (S : J ⥤ ShortComplex C) :
    IsColimit ((homologyFunctor C).mapCocone (colimit.cocone S)) where
  desc c := (exactIso S).inv ≫ colimit.desc (S ⋙ homologyFunctor C) c
  fac := sorry
  uniq := sorry

/-- The universal homology descent uses the specified reverse comparison. -/
@[simp]
theorem isColimitHomologyCocone_desc [HasColimitsOfShape J C]
    [(Limits.colim (J := J) (C := C)).PreservesHomology]
    (S : J ⥤ ShortComplex C) (s : Cocone (S ⋙ homologyFunctor C)) :
    (isColimitHomologyCocone S).desc s =
      (exactIso S).inv ≫ colimit.desc (S ⋙ homologyFunctor C) s := rfl

/-- If the colimit functor preserves homology, then the short-complex homology functor preserves
the colimit of every particular diagram of the given shape. -/
theorem preservesColimit_of_colim [HasColimitsOfShape J C]
    [(Limits.colim (J := J) (C := C)).PreservesHomology]
    (S : J ⥤ ShortComplex C) :
    PreservesColimit S (homologyFunctor C) :=
  preservesColimit_of_preserves_colimit_cocone
    (colimit.isColimit S) (isColimitHomologyCocone S)

end ColimitHomology

/-- Homology of short complexes preserves colimits of every shape for which colimits in the
ambient abelian category are exact. -/
noncomputable instance homologyFunctor_preservesColimitsOfShape_of_exact
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    PreservesColimitsOfShape J (homologyFunctor C) where
  preservesColimit := fun {S} ↦ ColimitHomology.preservesColimit_of_colim S

end CategoryTheory.ShortComplex
