module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.Vanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.DerivedQCoh

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DerivedQCoh
namespace ProperDualizingComplex

/- Lemma 53.6.3: in Situation 53.6.2, for a coherent exact sequence from the
curve dualizing module to `F` ending in `Q ⟶ 0` and with `H¹(X, Q) = 0`, either
`H¹(X, F) = 0` or `F` is isomorphic to the biproduct of the curve dualizing module
and `Q`.
-/
@[stacks 0B5E "main result"]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.firstCohomology_isZero_or_isomorphic_biprod :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (F Q : X.left.Modules) [F.IsCoherent] [Q.IsCoherent]
    (ι : curveDualizingModule X.hom ⟶ F) (π : F ⟶ Q)
    (h_zero : ι ≫ π = 0)
    (h_exact : (ShortComplex.mk ι π h_zero).Exact) [Epi π]
    (hQ : IsZero (Scheme.Hom.cohomology X.hom Q 1)),
    IsZero (Scheme.Hom.cohomology X.hom F 1) ∨
      IsIsomorphic F (curveDualizingModule X.hom ⊞ Q))

/- Lemma 53.6.3 (support-dimension corollary): zero-dimensional support supplies the vanishing
hypothesis for `Q`.
-/
@[stacks 0B5E "support-dimension corollary"]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.firstCohomology_isZero_or_isomorphic_biprod_of_supportDimension_le_zero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (F Q : X.left.Modules) [F.IsCoherent] [Q.IsCoherent]
    (ι : curveDualizingModule X.hom ⟶ F) (π : F ⟶ Q)
    (h_zero : ι ≫ π = 0)
    (h_exact : (ShortComplex.mk ι π h_zero).Exact) [Epi π]
    (h_support : topologicalKrullDim (RingedSpace.moduleSupport Q) ≤ 0),
    IsZero (Scheme.Hom.cohomology X.hom F 1) ∨
      IsIsomorphic F (curveDualizingModule X.hom ⊞ Q))

end ProperDualizingComplex
end DerivedQCoh
end Scheme
end AlgebraicGeometry
