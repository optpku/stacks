module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.StableContraction
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
universe u
@[expose] public section
namespace AlgebraicGeometry
/- Lemma 53.25.2 (1) -/
@[stacks 0E7Q] #check (AlgebraicGeometry.stableModelContraction :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hXdim : topologicalKrullDim X.left = 1)
    (hXsections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (hXgenus : 2 ≤ SchemeOverField.genus X hXdim hXsections)
    (hXnodal : SchemeOverField.atWorstNodal X),
    ∃ (Y : SchemeOverField k) (c : X ⟶ Y), StableContraction c)
/- Lemma 53.25.2 (2) -/
@[stacks 0E7Q] #check (AlgebraicGeometry.stableModelContraction_unique :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hXdim : topologicalKrullDim X.left = 1)
    (hXsections : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (hXgenus : 2 ≤ SchemeOverField.genus X hXdim hXsections)
    (hXnodal : SchemeOverField.atWorstNodal X)
    {Y₁ Y₂ : SchemeOverField k} {c₁ : X ⟶ Y₁} {c₂ : X ⟶ Y₂}
    (hc₁ : StableContraction c₁) (hc₂ : StableContraction c₂),
    ∃! e : Y₁ ≅ Y₂, c₁ ≫ e.hom = c₂)
end AlgebraicGeometry
