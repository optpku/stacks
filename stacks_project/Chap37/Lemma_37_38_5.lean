module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing.Separable

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.38.5: a smooth morphism at a fibrewise closed point with separable
residue-field extension admits an immersion through the point which is étale
over the base and whose fibre is set-theoretically that singleton. -/
@[stacks 057G] #check
  (AlgebraicGeometry.Scheme.Hom.SmoothAt.exists_immersion_etale_fiber_eq_singleton :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {x : X} (hf : f.SmoothAt x)
      (hclosed : f.asFiber x ∈ closedPoints (f.fiber (f x)))
      [hsep : Algebra.IsSeparableOver (S.residueField (f x)) (X.residueField x)],
      ∃ Z : Scheme.{u},
        ∃ i : Z ⟶ X,
          ∃ hxZ : x ∈ Set.range i,
            ∃ hi : IsImmersion i,
              ∃ hetale : Etale (i ≫ f),
                Set.range ((i ≫ f).fiberι (f x) ≫ i) = {x})

end AlgebraicGeometry.Scheme.Hom
