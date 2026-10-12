/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Additive
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Coherent
public import ReasLib.RingTheory.Coherent.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

namespace ModuleCat

/-- A coherent-ring filtered-colimit extension of a left exact functor on finitely presented
modules is additive. -/
theorem filteredColimitExtension_additive_of_coherent
    {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
    [PreservesFiniteLimits F]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
    [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J] [HasColimitsOfShape J B]
      {X Y : J ⥤ B} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)] :
    F'.Additive := sorry

/-- Under the coherent-ring hypotheses, the filtered-colimit extension of a left exact functor
on finitely presented modules preserves finite limits. -/
theorem filteredColimitExtension_preservesFiniteLimits_of_coherent
    {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
    [PreservesFiniteLimits F]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
    [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J] [HasColimitsOfShape J B]
      {X Y : J ⥤ B} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)] :
    PreservesFiniteLimits F' := sorry

/-- Under the coherent-ring hypotheses, the filtered-colimit extension of a left exact functor
on finitely presented modules preserves coproducts indexed by any type in the module universe. -/
theorem filteredColimitExtension_preservesCoproducts_of_coherent
    {A : Type u} [CommRing A] [IsCoherentRing A] {B : Type w} [Category.{z} B]
    [Preadditive B] [HasFiniteBiproducts B] [HasKernels B]
    [HasFilteredColimitsOfSize.{max u v, max u v} B]
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
    [PreservesFiniteLimits F]
    (F' : ModuleCat.{max u v} A ⥤ B)
    [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
    (eF' : (isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
    [∀ (J : Type (max u v)) [Category.{max u v} J] [IsFiltered J] [HasColimitsOfShape J B]
      {X Y : J ⥤ B} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) (colim : (J ⥤ B) ⥤ B)]
    (J : Type (max u v)) :
    PreservesColimitsOfShape (Discrete J) F' := sorry

end ModuleCat
