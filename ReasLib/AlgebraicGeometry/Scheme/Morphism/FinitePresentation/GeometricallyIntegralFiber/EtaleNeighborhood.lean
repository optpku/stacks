module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyConnectedFiber.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal.FiberCriterion
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Connected

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A normal finitely presented morphism and a geometrically irreducible open in one fibre admit,
after an affine elementary étale base change, a quasi-compact open with geometrically integral
fibres recovering the prescribed open. -/
theorem exists_compactOpen_geometricallyIntegral_after_elementaryEtale {Y S : Scheme.{u}}
    (h : Y ⟶ S) [FinitePresentation h] [Normal h] (s : S) (T : (h.fiber s).Opens)
    [GeometricallyIrreducible (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ U : Scheme.EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let g := E.toEtale.hom
      let P := pullback h g
      let p := pullback.snd h g
      let q := pullback.fst h g
      let β := baseChangeFiberMap h g q p (.of_hasPullback h g) E.point
      ∃ (_ : IsAffine E.toEtale.left) (V : P.Opens) (_ : IsCompact (V : Set P))
        (_ : GeometricallyIntegral (V.ι ≫ p)),
        p.fiberι E.point ⁻¹ᵁ V = β ⁻¹ᵁ (E.map_point.symm ▸ T) := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
