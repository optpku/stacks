/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology.Vanishing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.6: let `X` be a proper, reduced, connected, one-dimensional scheme
over a field, let `L` be an invertible module on `X`, and let `Z` be a zero-dimensional
closed subscheme. If `H¹(X, Z.toModule ⊗ L)` is nonzero, then some reduced, connected,
one-dimensional closed subscheme `Y` satisfies
`deg(L|_Y) ≤ -2 * χ(Y, 𝒪_Y) + deg(Z ∩ Y)`, where `Z ∩ Y` is the
scheme-theoretic intersection cut out by `Z ⊔ Y`. -/
@[stacks 0E3E] #check
  (AlgebraicGeometry.SchemeOverField.exists_connectedSubscheme_degree_le_of_cohomology_one_nonzero :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [IsReduced X.left] [ConnectedSpace X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (Z : X.left.IdealSheafData)
      (hZ_dimension : topologicalKrullDim Z.subscheme = 0)
      (hH1 : ¬ IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 1)),
      ∃ (Y : X.left.IdealSheafData)
          (hY_dimension : topologicalKrullDim Y.subscheme = 1),
        IsReduced Y.subscheme ∧ ConnectedSpace Y.subscheme ∧
          (let _ : (SheafOfModules.unit Y.subscheme.ringCatSheaf : Y.subscheme.Modules).IsCoherent :=
              @Scheme.Modules.structureSheaf_isCoherent Y.subscheme
                (LocallyOfFiniteType.isLocallyNoetherian (Y.subschemeι ≫ X.hom));
            Scheme.Modules.curveDegreeOfInvertible (Y.subschemeι ≫ X.hom)
                hY_dimension.le ((Scheme.Modules.pullback Y.subschemeι).obj L) ≤
              -2 * Scheme.Hom.eulerCharacteristic (Y.subschemeι ≫ X.hom)
                (SheafOfModules.unit Y.subscheme.ringCatSheaf : Y.subscheme.Modules) +
                (Module.finrank k
                  (Scheme.Hom.globalSectionsAlg ((Z ⊔ Y).subschemeι ≫ X.hom)) : ℤ)))

end AlgebraicGeometry.SchemeOverField
