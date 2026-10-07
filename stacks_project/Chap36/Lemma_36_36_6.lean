module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.CoveringIdeals
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 36.36.6: for a finite affine open cover with finite-type ideal sheaves supported on the
respective closed complements, the scheme has the resolution property exactly when every covering
ideal is an epimorphic quotient of a finite locally free module. -/
@[stacks 0F89] #check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_iff_coveringIdealQuotients :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {m : ℕ}
      (U : Fin m → X.affineOpens)
      (hU : TopologicalSpace.IsOpenCover (fun j ↦ (U j : X.Opens)))
      (I : Fin m → X.IdealSheafData) (hI : ∀ j, (I j).IsFiniteType)
      (hIU : ∀ j, (I j).support = (U j : X.Opens).compl),
      AlgebraicGeometry.Scheme.HasResolutionProperty X ↔
        ∀ j, ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
          (q : E ⟶ ((I j).toModule : X.Modules)), Epi q)
