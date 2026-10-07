module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Boundary
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open RingedSpace.DeRham.PuncturedLineBundle

universe u

/- Lemma 50.10.3: the shifted punctured-line-bundle residue boundary is the action of
the independently constructed relative de Rham first Chern class. -/
@[stacks 0FUG] #check
  (@AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.boundary_eq_classAction :
    ∀ {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
      (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
      [Scheme.IsRelativeSpectrumOver P] (D : WeightZeroDeRham f ℒ P),
      IsGeometric f ℒ P D →
        boundary f ℒ P D (puncturedLineBundleSequence_shortExact f ℒ P D) =
          Scheme.DeRham.CanonicalAction.map f 2 (Scheme.DeRham.firstChernClass f ℒ))
