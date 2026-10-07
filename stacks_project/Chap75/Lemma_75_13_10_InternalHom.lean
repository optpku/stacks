module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent

/-!
# Quasi-coherence of derived internal Hom on algebraic spaces

Derived internal Hom of a pseudo-coherent source into a bounded-below quasi-coherent target,
or of a perfect source into an unbounded quasi-coherent target, remains in `D_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

/-- Derived internal Hom from a pseudo-coherent object of `D(𝒪_X)` to a bounded-below object
of `D_QCoh(𝒪_X)` again has quasi-coherent cohomology. -/
theorem derivedQCoh_of_pseudoCoherent {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (K : ModuleDerived X) (L : DerivedQCoh X) (hK : IsPseudoCoherent X K)
    (hL : (t.plus : ObjectProperty (ModuleDerived X)) L.obj) :
    derivedQuasiCoherentModuleProperty X ((ihomOf H K).obj L.obj) := sorry

/-- Derived internal Hom from a perfect object of `D(𝒪_X)` to an object of `D_QCoh(𝒪_X)`
again has quasi-coherent cohomology. -/
theorem derivedQCoh_of_perfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X)] (H : MonoidalClosed (ModuleDerived X))
    (K : ModuleDerived X) (L : DerivedQCoh X) (hK : ModuleDerived.IsPerfect K) :
    derivedQuasiCoherentModuleProperty X ((ihomOf H K).obj L.obj) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
