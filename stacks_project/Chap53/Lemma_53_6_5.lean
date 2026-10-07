module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve.GlobalGeneration

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

universe u

/- Lemma 53.6.5: in Situation 53.6.2, let
`curveDualizingModule X.hom ⟶ F ⟶ Q ⟶ 0` be an exact sequence of coherent
modules. Assume that `moduleSupport Q` has topological Krull dimension zero,
that `H⁰(X, Q)` has dimension at least two over `k`, and that every submodule
of `F` mapping injectively to `Q` is zero. Then the map to `Q` induced by all
global sections of `F` is an epimorphism. -/
@[stacks 0B5F] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.globalSectionsToQuotient_epi :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (F Q : X.left.Modules) [F.IsCoherent] [Q.IsCoherent]
    (ι : curveDualizingModule X.hom ⟶ F) (π : F ⟶ Q)
    (h_zero : ι ≫ π = 0)
    (h_exact : (ShortComplex.mk ι π h_zero).Exact) [Epi π]
    (h_support : topologicalKrullDim (RingedSpace.moduleSupport Q) = 0)
    (h_sections : 2 ≤ Scheme.Hom.cohomologyFinrank X.hom Q 0)
    (h_no_submodule : ∀ Q' : Subobject F,
      Mono (Q'.arrow ≫ π) → IsZero (Q' : X.left.Modules)),
    Epi (F.freeHomEquiv.symm (fun s ↦ s) ≫ π))
