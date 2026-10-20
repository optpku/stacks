/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy

/-!
# Functors out of a DG homotopy category

The quotient functor from closed degree-zero morphisms to DG homotopy classes is dense enough
to detect and construct natural transformations.  This leaf packages that universal-property
API independently of shifts, triangulations, and any particular differential graded category.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor

noncomputable section

universe u v w e z

namespace DifferentialGradedCategory.Comp.InK

variable {R : Type u} [CommRing R]
variable {C : Type v} [DifferentialGradedCategory.{u, v, w} R C]
variable {E : Type e} [Category.{z} E]

/-- Natural transformations out of `K R C` are determined after precomposition with the
canonical quotient functor from closed degree-zero morphisms. -/
@[stacks 09KX "natural transformations out of a DG homotopy category are detected before quotient"]
theorem natTrans_ext {F G : K R C ⥤ E} (f g : F ⟶ G)
    (h : whiskerLeft (inKFunctor : Comp R C ⥤ K R C) f =
      whiskerLeft (inKFunctor : Comp R C ⥤ K R C) g) :
    f = g := sorry

/-- Lift a natural transformation defined after precomposition with `Comp.inKFunctor` to the
DG homotopy category. -/
@[stacks 09KX "lift a natural transformation through the DG homotopy quotient"]
def natTransLift {F G : K R C ⥤ E}
    (f : (inKFunctor : Comp R C ⥤ K R C) ⋙ F ⟶
      (inKFunctor : Comp R C ⥤ K R C) ⋙ G) :
    F ⟶ G where
  app := fun ⟨X⟩ ↦ f.app ⟨X⟩
  naturality := sorry

/-- The lift of a natural transformation has the prescribed component on every object coming
from the closed degree-zero category. -/
@[simp, stacks 09KX "components of a lifted transformation through the DG homotopy quotient"]
theorem natTransLift_app {F G : K R C ⥤ E}
    (f : (inKFunctor : Comp R C ⥤ K R C) ⋙ F ⟶
      (inKFunctor : Comp R C ⥤ K R C) ⋙ G)
    (X : Comp R C) :
    (natTransLift f).app X.inK = f.app X := sorry

/-- Lifting and then restricting a natural transformation along `Comp.inKFunctor` recovers the
original transformation. -/
@[stacks 09KX "restriction of a lifted transformation through the DG homotopy quotient"]
theorem whiskerLeft_natTransLift {F G : K R C ⥤ E}
    (f : (inKFunctor : Comp R C ⥤ K R C) ⋙ F ⟶
      (inKFunctor : Comp R C ⥤ K R C) ⋙ G) :
    whiskerLeft (inKFunctor : Comp R C ⥤ K R C) (natTransLift f) = f := sorry

/-- Lift a natural isomorphism defined after precomposition with `Comp.inKFunctor` to the DG
homotopy category. -/
@[stacks 09KX "lift a natural isomorphism through the DG homotopy quotient"]
def natIsoLift {F G : K R C ⥤ E}
    (e : (inKFunctor : Comp R C ⥤ K R C) ⋙ F ≅
      (inKFunctor : Comp R C ⥤ K R C) ⋙ G) :
    F ≅ G where
  hom := natTransLift e.hom
  inv := natTransLift e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward component of a lifted natural isomorphism is the lift of its forward
transformation. -/
@[simp, stacks 09KX "forward map of an isomorphism lifted through the DG homotopy quotient"]
theorem natIsoLift_hom {F G : K R C ⥤ E}
    (e : (inKFunctor : Comp R C ⥤ K R C) ⋙ F ≅
      (inKFunctor : Comp R C ⥤ K R C) ⋙ G) :
    (natIsoLift e).hom = natTransLift e.hom := sorry

/-- Precomposition with the quotient functor is full on functor categories. -/
@[stacks 09KX "fullness of precomposition with the DG homotopy quotient"]
instance whiskeringLeft_full :
    ((Functor.whiskeringLeft (Comp R C) (K R C) E).obj
      (inKFunctor : Comp R C ⥤ K R C)).Full where
  map_surjective f := ⟨natTransLift f, whiskerLeft_natTransLift f⟩

/-- Precomposition with the quotient functor is faithful on functor categories. -/
@[stacks 09KX "faithfulness of precomposition with the DG homotopy quotient"]
instance whiskeringLeft_faithful :
    ((Functor.whiskeringLeft (Comp R C) (K R C) E).obj
      (inKFunctor : Comp R C ⥤ K R C)).Faithful where
  map_injective h := natTrans_ext _ _ h

end DifferentialGradedCategory.Comp.InK
