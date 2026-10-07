module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.GlobalGeneration

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.DerivedQCoh

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/- Lemma 53.6.6: in Situation 53.6.2, suppose that `X` is integral and that
`0 ⟶ curveDualizingModule X.hom ⟶ F ⟶ Q ⟶ 0` is a short exact sequence of
coherent modules. If `F` is torsion free, `moduleSupport Q` has topological
Krull dimension zero, and `H⁰(X, Q)` has dimension at least two over `k`, then
`F` is globally generated. -/
@[stacks 0B5G] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.isGloballyGenerated_of_torsionFree :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [IsIntegral X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (F Q : X.left.Modules) [F.IsCoherent] [Q.IsCoherent]
    [Scheme.Modules.IsTorsionFree F]
    (ι : curveDualizingModule X.hom ⟶ F) (π : F ⟶ Q)
    (h_zero : ι ≫ π = 0)
    (h_short : (ShortComplex.mk ι π h_zero).ShortExact)
    (h_support : topologicalKrullDim (RingedSpace.moduleSupport Q) = 0)
    (h_sections : 2 ≤ Scheme.Hom.cohomologyFinrank X.hom Q 0),
    SheafOfModules.IsGloballyGenerated F)

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
