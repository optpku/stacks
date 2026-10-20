module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.GeometricallyConnectedFiber
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.FinitePresentation

/-- A flat finitely presented morphism with geometrically reduced fibres and a geometrically
connected open in one fibre admits, after an affine elementary étale base change, a quasi-compact
open with geometrically connected fibres recovering the prescribed open. -/
theorem exists_compactOpen_geometricallyConnected_after_elementaryEtale {Y S : Scheme.{u}}
    (h : Y ⟶ S) [FinitePresentation h] [Flat h] [GeometricallyReduced h]
    (s : S) (T : (h.fiber s).Opens)
    [GeometricallyConnected (T.ι ≫ h.fiberToSpecResidueField s)] :
    ∃ U : Scheme.EtaleNeighborhood.Elementary S s,
      let E := U.obj
      let g := E.toEtale.hom
      let P := pullback h g
      let p := pullback.snd h g
      let q := pullback.fst h g
      let β := baseChangeFiberMap h g q p (.of_hasPullback h g) E.point
      ∃ (_ : IsAffine E.toEtale.left) (V : P.Opens) (_ : IsCompact (V : Set P))
        (_ : GeometricallyConnected (V.ι ≫ p)),
        p.fiberι E.point ⁻¹ᵁ V = β ⁻¹ᵁ (E.map_point.symm ▸ T) := sorry

end AlgebraicGeometry.Scheme.Hom.FinitePresentation
