/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.DiagramHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact limits and homology of short complexes

An exact limit functor commutes with the homology of short complexes. The primary comparison is
stated for an arbitrary diagram shape; the product comparison is its discrete specialization.
Projection formulas are part of the public API, so applications do not need to unfold the
construction through the short-complex/functor-category equivalence.
-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits

noncomputable section

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type u'} [Category.{v'} J]

namespace LimitHomology

/- The arbitrary-limit comparison belongs next to its pointwise comparison data. -/
/-- The canonical comparison from homology of a limit to the limit of the homology diagram. -/
@[stacks 060K]
noncomputable def iso (S : J ⥤ ShortComplex C) [HasLimit S]
    [PreservesLimit S (homologyFunctor C)] :
    (limit S).homology ≅ limit (S ⋙ homologyFunctor C) :=
  preservesLimitIso (homologyFunctor C) S

namespace iso

/-- The comparison between limit homology and the limit of homology is characterized by its
composites with the limit projections. -/
@[reassoc (attr := simp)]
theorem hom_π (S : J ⥤ ShortComplex C) [HasLimit S]
    [PreservesLimit S (homologyFunctor C)] (j : J) :
    (iso S).hom ≫ limit.π (S ⋙ homologyFunctor C) j =
      homologyMap (limit.π S j) := sorry

/-- The inverse limit-homology comparison followed by the homology map of a limit projection is
the corresponding limit-of-homology projection. -/
@[reassoc (attr := simp)]
theorem inv_homologyMap (S : J ⥤ ShortComplex C) [HasLimit S]
    [PreservesLimit S (homologyFunctor C)] (j : J) :
    (iso S).inv ≫ homologyMap (limit.π S j) =
      limit.π (S ⋙ homologyFunctor C) j := sorry

/-- The limit-homology comparison is natural in the diagram of short complexes. -/
@[reassoc]
theorem naturality [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J (homologyFunctor C)]
    {S T : J ⥤ ShortComplex C} (f : S ⟶ T) :
    homologyMap (Limits.lim.map f) ≫ (iso T).hom =
      (iso S).hom ≫
        Limits.lim.map (Functor.whiskerRight f (homologyFunctor C)) := sorry

end iso

/-- If the limit functor preserves homology, then the short-complex homology functor preserves
the limit of every particular diagram of the given shape. -/
theorem preservesLimit_of_lim [HasLimitsOfShape J C]
    [(Limits.lim (J := J) (C := C)).PreservesHomology]
    (S : J ⥤ ShortComplex C) :
    PreservesLimit S (homologyFunctor C) := sorry

end LimitHomology

/-- Homology of short complexes preserves limits of every shape for which limits in the ambient
abelian category are exact. -/
noncomputable instance homologyFunctor_preservesLimitsOfShape_of_exact
    [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] :
    PreservesLimitsOfShape J (homologyFunctor C) := sorry

section Products

variable {I : Type u'} [HasProductsOfShape I C]
  [HasExactLimitsOfShape (Discrete I) C]

namespace PiHomology

/- The product comparison is the discrete-shape specialization of `LimitHomology.iso`. -/
/-- Homology of short complexes commutes canonically with an exact product. -/
noncomputable def iso (S : I → ShortComplex C) :
    (∏ᶜ S).homology ≅ ∏ᶜ fun i ↦ (S i).homology :=
  LimitHomology.iso (Discrete.functor S) ≪≫
    (Pi.isoLimit (Discrete.functor S ⋙ homologyFunctor C)).symm

namespace iso

/-- The exact-product homology comparison has the expected component at every factor. -/
@[reassoc (attr := simp)]
theorem hom_π (S : I → ShortComplex C) (i : I) :
    (iso S).hom ≫ Pi.π (fun j ↦ (S j).homology) i =
      homologyMap (Pi.π S i) := sorry

/-- The inverse exact-product homology comparison followed by the homology map of a product
projection is the corresponding projection from the product of homology objects. -/
@[reassoc (attr := simp)]
theorem inv_homologyMap (S : I → ShortComplex C) (i : I) :
    (iso S).inv ≫ homologyMap (Pi.π S i) =
      Pi.π (fun j ↦ (S j).homology) i := sorry

end iso

end PiHomology

end Products

end CategoryTheory.ShortComplex
