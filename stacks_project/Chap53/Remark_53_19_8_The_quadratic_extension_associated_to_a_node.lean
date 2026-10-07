module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.NodalLocalRing
public import ReasLib.RingTheory.LocalRing.Nodal

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

/- Remark 53.19.8 (The quadratic extension associated to a node) -/
@[stacks 0CBT] #check
  (NodalLocalRing.quadraticAlgebra_spec :
    ∀ (k : Type u) [Field k]
      (A : Type u) [CommRing A] [IsLocalRing A] [Algebra k A] [IsNodalLocalRing A]
      [Algebra.IsSeparableOver k (ResidueField A)],
    Module.finrank (ResidueField A) (NodalLocalRing.quadraticAlgebra A) = 2 ∧
      Algebra.IsSeparable (ResidueField A) (NodalLocalRing.quadraticAlgebra A))

#check NodalLocalRing.quadraticPresentation_equiv
#check NodalLocalRing.normalizationFiber_equiv
#check NodalLocalRing.associatedGradedProj_iso
#check NodalLocalRing.normalizationFiber_iso_specQuadraticAlgebra
