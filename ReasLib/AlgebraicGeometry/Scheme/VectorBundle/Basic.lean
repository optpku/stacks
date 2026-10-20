module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction

/-!
# Vector bundles associated to quasi-coherent module sheaves

This file defines the total space and structural morphism of the vector bundle associated to a
quasi-coherent module sheaf, using an explicit chosen model of its relative spectrum.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} (ℱ : S.Modules) [ℱ.IsQuasicoherent]

/-- The vector bundle associated to `ℱ`, represented by the explicit relative-spectrum model
`P` of its symmetric algebra. -/
noncomputable def associatedVectorBundle
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℱ))
    [IsRelativeSpectrumOver P] : Scheme.{u} :=
  relativeSpec P

/-- The structural morphism from the vector bundle associated to `ℱ` to its base scheme. -/
noncomputable def associatedVectorBundleπ
    (P : RelativeSpectrumOver (SymmetricAlgebra.qcAlgebra ℱ))
    [IsRelativeSpectrumOver P] : associatedVectorBundle ℱ P ⟶ S :=
  relativeSpecπ P

end AlgebraicGeometry.Scheme
