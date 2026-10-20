module

public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of Short Complexes

Mathlib constructs colimits of short complexes componentwise. This file bundles that cocone as
a `ColimitCocone`, records the canonical comparison with the chosen categorical colimit, and
specializes its legs to short complexes owned in a functor category.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {J : Type u'} [Category.{v'} J] [HasColimitsOfShape J C]

namespace Colimit

/-- The componentwise colimit cocone of a diagram of short complexes, bundled with its universal
property. -/
noncomputable def cocone (S : J ⥤ ShortComplex C) : ColimitCocone S where
  cocone := ShortComplex.colimitCocone S
  isColimit := ShortComplex.isColimitColimitCocone S

/-- The canonical isomorphism from the chosen colimit of a short-complex diagram to its
componentwise colimit. -/
noncomputable def iso (S : J ⥤ ShortComplex C) :
    colimit S ≅ (ShortComplex.colimitCocone S).pt :=
  colimit.isoColimitCocone (cocone S)

namespace iso

/-- The canonical componentwise-colimit isomorphism intertwines every chosen colimit leg with
the corresponding componentwise cocone leg. -/
@[reassoc (attr := simp)]
theorem ι_hom (S : J ⥤ ShortComplex C) (j : J) :
    colimit.ι S j ≫ (iso S).hom =
      (ShortComplex.colimitCocone S).ι.app j := sorry

/-- Every componentwise cocone leg followed by the inverse comparison is the corresponding
chosen colimit leg. -/
@[reassoc (attr := simp)]
theorem ι_inv (S : J ⥤ ShortComplex C) (j : J) :
    (ShortComplex.colimitCocone S).ι.app j ≫ (iso S).inv =
      colimit.ι S j := sorry

namespace functorEquivalence

/-- The chosen-colimit comparison for a short complex owned in a functor category has the
expected stage-to-colimit leg. -/
@[reassoc]
theorem ι_hom (S : ShortComplex (J ⥤ C)) (j : J) :
    colimit.ι ((ShortComplex.functorEquivalence J C).functor.obj S) j ≫
        (Colimit.iso ((ShortComplex.functorEquivalence J C).functor.obj S)).hom =
      S.mapNatTrans (Limits.colim.ι (J := J) (C := C) j) := sorry

end functorEquivalence

end iso

end Colimit

namespace colimitCocone

/-- For a short complex in a functor category, the componentwise colimit cocone leg is induced by
the canonical natural transformation from evaluation to the colimit functor. -/
@[simp]
theorem ι_functorEquivalence (S : ShortComplex (J ⥤ C)) (j : J) :
    (ShortComplex.colimitCocone
      ((functorEquivalence J C).functor.obj S)).ι.app j =
      S.mapNatTrans (Limits.colim.ι (J := J) (C := C) j) := sorry

end colimitCocone

end CategoryTheory.ShortComplex
