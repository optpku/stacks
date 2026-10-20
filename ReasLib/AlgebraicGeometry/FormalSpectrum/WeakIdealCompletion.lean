module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Taut
public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleCompletion
public import ReasLib.AlgebraicGeometry.FormalSpectrum.Representable

/-!
# Representability of formal spectra of weak-ideal completions

The canonical morphism from the formal spectrum of a weak-ideal completion to
the formal spectrum of its base ring is representable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
  (A : Type u) [CommRing A] [Algebra B A]

/-- The formal-spectrum morphism induced by the canonical weak-ideal completion
map is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces_spfMap_weakIdealCompletion :
    AlgebraicSpace.representableByAlgebraicSpaces
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hB A)) :=
  sorry

/-- The formal-spectrum morphism induced by the canonical weak-ideal completion
map is representable by schemes. -/
theorem relativelyRepresentable_spfMap_weakIdealCompletion :
    yoneda.relativelyRepresentable
      ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type u)).map
        (spfMap_weakIdealCompletion hB A)) :=
  sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
