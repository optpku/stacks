/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyIntegralFiber.EtaleNeighborhood

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/- Lemma 37.46.4: a normal finitely presented morphism and a geometrically irreducible open in
one fibre admit, after an affine elementary étale base change, a quasi-compact open with
geometrically integral fibres recovering the prescribed open. -/
@[stacks 057J] #check
  (AlgebraicGeometry.Scheme.Hom.FinitePresentation.exists_compactOpen_geometricallyIntegral_after_elementaryEtale :
    {Y S : Scheme.{u}} →
    (h : Y ⟶ S) → [FinitePresentation h] → [AlgebraicGeometry.Normal h] →
    (s : S) → (T : (h.fiber s).Opens) →
    [AlgebraicGeometry.GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)] →
    ∃ U : Scheme.EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let g := E.toEtale.hom
      let P := pullback h g
      let p := pullback.snd h g
      let q := pullback.fst h g
      let β := baseChangeFiberMap h g q p (.of_hasPullback h g) E.point
      ∃ (_ : IsAffine E.toEtale.left) (V : P.Opens) (_ : IsCompact (V : Set P))
        (_ : GeometricallyIntegral (V.ι ≫ p)),
        p.fiberι E.point ⁻¹ᵁ V = β ⁻¹ᵁ (E.map_point.symm ▸ T))

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
