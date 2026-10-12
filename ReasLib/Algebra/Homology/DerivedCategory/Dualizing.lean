/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory

/-- A derived module complex over a Noetherian commutative ring is dualizing relative to a
selected closed-monoidal presentation when it has finite injective dimension, finite cohomology
modules in every degree, and invertible canonical homothety. -/
structure IsDualizingComplex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) : Prop where
  /-- The complex has finite injective dimension. -/
  finiteInjectiveDimension : K.HasFiniteInjectiveDimension
  /-- Every cohomology module of the complex is finite. -/
  finiteCohomology :
    ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)
  /-- The canonical homothety from the tensor unit to the derived endomorphism object is
  invertible. -/
  homothety_isIso :
    IsIso (@MonoidalClosed.curry'
      (DerivedCategory (ModuleCat.{u} A)) _ _ K K (H.closed K) (𝟙 K))

namespace IsDualizingComplex

/-- Construct the dualizing-complex property from its three defining conditions. -/
def ofConditions
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    {K : DerivedCategory (ModuleCat.{u} A)}
    {H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))}
    (h_injective : K.HasFiniteInjectiveDimension)
    (h_finite :
      ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (h_homothety :
      IsIso (@MonoidalClosed.curry'
        (DerivedCategory (ModuleCat.{u} A)) _ _ K K (H.closed K) (𝟙 K))) :
    K.IsDualizingComplex H :=
  ⟨h_injective, h_finite, h_homothety⟩

end IsDualizingComplex

/-- The defining conditions for a dualizing complex over a Noetherian commutative ring. -/
theorem isDualizingComplex_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A))
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))) :
    K.IsDualizingComplex H ↔
      K.HasFiniteInjectiveDimension ∧
        (∀ i : ℤ,
          Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ∧
        IsIso (@MonoidalClosed.curry'
          (DerivedCategory (ModuleCat.{u} A)) _ _ K K (H.closed K) (𝟙 K)) := sorry

end CategoryTheory.DerivedCategory
