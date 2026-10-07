module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.CohenMacaulay

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex
open scoped DerivedExt

universe u

/- Lemma 48.27.5 -/
@[stacks 0FVZ]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isDualizingModule :
  ∀ {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Scheme.CohenMacaulay X] [TopologicalSpace.EquidimensionalSpace X]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
    (d : ℕ) (_h_dimension : topologicalKrullDim X = d),
    AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule
      (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f).obj
      H (-(d : ℤ))
      (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule f))

#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_isCoherent
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.dualizingModule_cohenMacaulay
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.support_eq_univ
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_bijective
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_naturality
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_shift
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.serreComparison_distinguishedBoundary
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleSerreComparison_bijective
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.moduleSerreComparison_naturality
