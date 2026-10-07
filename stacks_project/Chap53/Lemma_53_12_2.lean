module

public import ReasLib.AlgebraicGeometry.Curve.RiemannHurwitz
public import ReasLib.AlgebraicGeometry.Curve.GenericallyEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.IdealSheafData
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.12.2: for a morphism of smooth proper curves over a field satisfying the
finite-separable function-field condition, with constant global functions and genera `gX` and
`gY`, the genus formula is `2 * gX - 2 = (2 * gY - 2) * deg(f) + deg(R)`, where `R` is the
effective Cartier divisor defined by the Kähler different. -/
@[stacks 0C1D]
#check (AlgebraicGeometry.Curve.riemannHurwitz :
    ∀ {k : Type u} [Field k] (X Y : SchemeOverField k)
    [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    [Smooth X.hom] [Smooth Y.hom] (f : X ⟶ Y)
    [LocallyOfFiniteType f.left] [IsDominant f.left]
    (h_finite : f.left.FiniteFunctionFieldExtension)
    (h_separable : f.left.SeparableFunctionFieldExtension)
    (hΓX : Function.Bijective (globalSectionsMap X.hom))
    (hΓY : Function.Bijective (globalSectionsMap Y.hom))
    (gX gY : ℕ)
    (h_genusX : gX = genus X
      (AlgebraicGeometry.topologicalKrullDim_eq_one X) hΓX)
    (h_genusY : gY = genus Y
      (AlgebraicGeometry.topologicalKrullDim_eq_one Y) hΓY),
    2 * (gX : ℤ) - 2 =
      (2 * (gY : ℤ) - 2) * (f.left.inducedFunctionFieldDegree : ℤ) +
        (Module.finrank k
          (globalSectionsAlg
            (subschemeι (kaehlerDifferent f.left) ≫ X.hom)) : ℤ))

end AlgebraicGeometry.Curve
