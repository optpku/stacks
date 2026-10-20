module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric.Lift

/-!
# Functoriality of symmetric algebras
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SymmetricAlgebra

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]

/-- The symmetric-algebra morphism induced by a morphism of quasi-coherent modules. -/
noncomputable def map (f : F ⟶ G) : qcAlgebra F ⟶ qcAlgebra G :=
  lift F (qcAlgebra G) (f ≫ ι G)

/-- The symmetric-algebra map agrees with the original module map on degree-one generators. -/
theorem map_ι (f : F ⟶ G) :
    ι F ≫ QcAlgebraUnder.underlyingModuleMap X (map f) = f ≫ ι G := sorry

end AlgebraicGeometry.Scheme.SymmetricAlgebra

