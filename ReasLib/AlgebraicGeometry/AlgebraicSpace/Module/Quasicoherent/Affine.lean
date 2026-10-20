module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Associated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Coherator

/-! # The coherator on affine algebraic spaces -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- On an affine algebraic space, the coherator is naturally isomorphic to global sections
followed by the associated quasi-coherent module functor. -/
theorem QCoh.affineCoherator_isomorphic {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAffine X] :
    IsIsomorphic (QCoh.coherator X) (moduleGlobalSectionsFunctor X ⋙ QCoh.tensorOX X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

