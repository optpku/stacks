module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect

/-!
# Quasi-coherence of derived internal Hom on algebraic spaces

Derived internal Hom is the chosen right adjoint to canonical fixed-right derived tensoring.
The `IsLeftAdjoint` premise expresses the existence needed to define this right adjoint.
It has quasi-coherent cohomology for a pseudo-coherent source and a bounded-below
quasi-coherent target, or for a perfect source and any quasi-coherent target.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

/-- The right adjoint to canonical fixed-right derived tensoring by a pseudo-coherent
object sends bounded-below quasi-coherent objects to objects with quasi-coherent cohomology,
assuming this right adjoint exists. -/
theorem derivedQCoh_of_pseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : ModuleDerived X) [(DerivedTensor.Right.functor K).IsLeftAdjoint]
    (L : DerivedQCoh X) (hK : IsPseudoCoherent X K)
    (hL : (t.plus : ObjectProperty (ModuleDerived X)) L.obj) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedTensor.Right.functor K).rightAdjoint.obj L.obj) := sorry

/-- The right adjoint to canonical fixed-right derived tensoring by a perfect object sends
quasi-coherent objects to objects with quasi-coherent cohomology, assuming this right adjoint
exists. -/
theorem derivedQCoh_of_perfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    (K : ModuleDerived X) [(DerivedTensor.Right.functor K).IsLeftAdjoint]
    (L : DerivedQCoh X) (hK : ModuleDerived.IsPerfect K) :
    derivedQuasiCoherentModuleProperty X
      ((DerivedTensor.Right.functor K).rightAdjoint.obj L.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
