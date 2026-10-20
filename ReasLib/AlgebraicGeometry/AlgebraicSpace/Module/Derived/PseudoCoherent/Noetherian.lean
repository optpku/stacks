module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent

/-!
# Pseudo-coherent complexes on Noetherian algebraic spaces

On a Noetherian algebraic space, pseudo-coherence of an object of `D_QCoh(𝒪_X)` is
characterized by bounded-above coherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- An object of `D_QCoh(𝒪_X)` on a Noetherian algebraic space is `m`-pseudo-coherent if and
only if it is bounded above and its cohomology sheaves in degrees at least `m` are
coherent. -/
theorem isMPseudoCoherent_iff_boundedAbove_and_cohomology_coherent_ge
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (E : DerivedQCoh X) (m : ℤ) :
    IsMPseudoCoherent X E.obj m ↔
      (t.minus : ObjectProperty (ModuleDerived X)) E.obj ∧
        ∀ i : ℤ, m ≤ i →
          ((DerivedCategory.homologyFunctor (Modules X) i).obj E.obj).IsCoherent :=
  sorry

/-- An object of `D_QCoh(𝒪_X)` on a Noetherian algebraic space is pseudo-coherent if and
only if it is bounded above and all of its cohomology sheaves are coherent. -/
theorem isPseudoCoherent_iff_boundedAbove_and_cohomology_coherent
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
    (E : DerivedQCoh X) :
    IsPseudoCoherent X E.obj ↔
      (t.minus : ObjectProperty (ModuleDerived X)) E.obj ∧
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent (structureSheaf X)) E.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
