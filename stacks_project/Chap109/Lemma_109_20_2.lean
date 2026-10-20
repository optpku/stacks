module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable
import StacksCheckRecall

/-!
# Prestable curves

There is an open substack 𝒞urves^{prestable} ⊂ 𝒞urves such that a family's
classifying morphism factors through it precisely when the family is prestable.
For a scheme X proper over a field k with dimension at most one, its classifying
morphism factors through this substack precisely when its singularities are
at-worst-nodal, its dimension is one, and the canonical map k → H⁰(X, 𝒪_X)
is an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.20.2: the prestable substack is open, and membership classifies
prestable families of curves. Over a field, a proper scheme of dimension at
most one belongs to it precisely when it is at-worst-nodal, has dimension one,
and its canonical map from the ground field to global functions is bijective. -/
@[stacks 0E6U] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_prestable_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        prestable S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestable_iff :
  ∀ {S : Scheme.{u}} (P : Obj S), prestable S P ↔ Prestable (hom P))

#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_prestable_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      prestable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        SchemeOverField.atWorstNodal X ∧
          topologicalKrullDim X.left = 1 ∧
          Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
