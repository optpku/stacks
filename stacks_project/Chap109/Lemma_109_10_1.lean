module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.GeometricallyReduced

/-!
# Geometrically reduced curves

There is an open substack 𝒞urves^{geomred} ⊂ 𝒞urves classifying families of
curves with geometrically reduced fibres, equivalently proper geometrically
reduced schemes of dimension at most one over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.10.1. Families with geometrically reduced fibres form an open
substack of curves, with the following family and field-valued characterizations. -/
@[stacks 0E0G] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_geometricallyReduced_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
        geometricallyReduced S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.geometricallyReduced_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
      geometricallyReduced S P ↔
        ∀ y : Points (ofOver (base P)), y ∈ geometricallyReducedFiberLocus (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_geometricallyReduced_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
      geometricallyReduced (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
        SchemeOverField.geometricallyReduced X)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
