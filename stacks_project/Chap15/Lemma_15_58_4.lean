module

import StacksCheckRecall
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.TotalFunctor.Triangulated

/-!
# Lemma 15.58.4

@stack 064J

The exactness assertion is a specialization of the reusable fixed-factor
bifunctor-totalization instances.  The `leftFixed` and `rightFixed` owners
keep the homotopy-category descent and its triangulated structure together,
so this chapter entry only exposes the two source-facing views.
-/

@[expose] public section

open CategoryTheory ComplexShape MonoidalCategory

universe u

variable {R : Type u} [CommRing R]
variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]
variable (P : CochainComplex (ModuleCat R) ℤ)

/- Lemma 15.58.4 (1): fixing the left complex gives an exact endofunctor of `K(R)`. -/
@[stacks 064J "left fixed-factor totalization is exact"]
#check (inferInstance :
  (Functor.Homotopy.BifunctorTotal.leftFixed (curriedTensor (ModuleCat R)) P).IsTriangulated)

/- Lemma 15.58.4 (2): fixing the right complex gives the symmetric exact endofunctor. -/
@[stacks 064J "right fixed-factor totalization is exact"]
#check (inferInstance :
  (Functor.Homotopy.BifunctorTotal.rightFixed (curriedTensor (ModuleCat R)) P).IsTriangulated)

#check @Functor.Homotopy.BifunctorTotal.leftFixed
#check @Functor.Homotopy.BifunctorTotal.rightFixed
#check @Functor.Homotopy.BifunctorTotal.leftFixedIsTriangulated
#check @Functor.Homotopy.BifunctorTotal.rightFixedIsTriangulated
