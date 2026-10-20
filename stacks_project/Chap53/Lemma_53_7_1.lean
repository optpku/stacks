module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.VeryAmple.DimensionOne
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.7.1: an ample invertible module on a proper one-dimensional scheme over a field,
with constant global functions, a regular global section, and vanishing first cohomology, has
relatively very ample sixth tensor power. -/
@[stacks 0E8V] #check
  (AlgebraicGeometry.SchemeOverField.relativelyVeryAmple_tensorPow_six :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (L : X.left.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
    (h_regular : ∃ s : L.sections, RingedSpace.IsRegularSection L s)
    (hH1 : IsZero (Scheme.Hom.cohomology X.hom L 1)),
    RelativelyVeryAmple X.hom (RingedSpace.TensorPower.sheaf L 6))

end AlgebraicGeometry.SchemeOverField
