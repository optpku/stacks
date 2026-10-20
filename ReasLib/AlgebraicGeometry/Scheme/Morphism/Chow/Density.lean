module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Chow

/-!
# Dense Chow modifications

This file records refinements of Chow modifications whose distinguished open has
scheme-theoretically dense preimage.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ChowLemmaModification

/-- A separated finite-type morphism to a Noetherian scheme admits a Chow modification for
which the preimage of the distinguished open is scheme-theoretically dense. -/
theorem exists_schemeTheoreticallyDense_preimage
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f] :
    ∃ M : ChowLemmaModification f,
      schemeTheoreticallyDense (M.π ⁻¹ᵁ M.denseOpen) := sorry

/-- If the source of a separated finite-type morphism to a Noetherian scheme is reduced, it
admits a Chow modification with reduced source and scheme-theoretically dense distinguished
open preimage. -/
theorem exists_schemeTheoreticallyDense_preimage_isReduced
    {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [IsSeparated f]
    [Scheme.Hom.FiniteType f] [IsReduced X] :
    ∃ M : ChowLemmaModification f,
      schemeTheoreticallyDense (M.π ⁻¹ᵁ M.denseOpen) ∧ IsReduced M.X' := sorry

end AlgebraicGeometry.ChowLemmaModification
