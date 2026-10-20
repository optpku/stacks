module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower.Affine.QuasiCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.ProperSupport

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
  [IsAdicComplete I A] {X : AlgebraicSpace (Spec (CommRingCat.of A))}
  [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)]

/-- Over an adically complete Noetherian affine base, coherent completion on a finite-type
separated algebraic space is bijective on morphisms when the support intersection is proper. -/
theorem homMap_bijective (ℱ 𝒢 : Coh X)
    (h_support : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (closedSupport ℱ.obj ⊓ closedSupport 𝒢.obj)) :
    Function.Bijective fun f : ℱ ⟶ 𝒢 ↦
      (functor (pullbackIdeal I (SchemeRealization.toBase X))).map f := sorry

/-- Over an adically complete Noetherian affine base, coherent completion on a finite-type
separated algebraic space is injective on morphisms when the support intersection is proper. -/
theorem homMap_injective (ℱ 𝒢 : Coh X)
    (h_support : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (closedSupport ℱ.obj ⊓ closedSupport 𝒢.obj)) :
    Function.Injective fun f : ℱ ⟶ 𝒢 ↦
      (functor (pullbackIdeal I (SchemeRealization.toBase X))).map f := sorry

/-- Over an adically complete Noetherian affine base, coherent completion on a finite-type
separated algebraic space is surjective on morphisms when the support intersection is proper. -/
theorem homMap_surjective (ℱ 𝒢 : Coh X)
    (h_support : ClosedSubset.ProperOver (SchemeRealization.toBase X)
      (closedSupport ℱ.obj ⊓ closedSupport 𝒢.obj)) :
    Function.Surjective fun f : ℱ ⟶ 𝒢 ↦
      (functor (pullbackIdeal I (SchemeRealization.toBase X))).map f := sorry

end AlgebraicGeometry.AlgebraicSpace.CoherentCompletion

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Over an adically complete Noetherian affine base, coherent completion on a finite-type
separated algebraic space, restricted to modules with proper support, is full. -/
instance instFull_coherentProperSupportCompletionFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)] :
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).Full := sorry

/-- Over an adically complete Noetherian affine base, coherent completion on a finite-type
separated algebraic space, restricted to modules with proper support, is faithful. -/
instance instFaithful_coherentProperSupportCompletionFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)] :
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).Faithful := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
