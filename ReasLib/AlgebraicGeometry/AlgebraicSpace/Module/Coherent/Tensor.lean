module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal

/-!
# Tensor products of coherent modules on algebraic spaces

The tensor product of coherent modules on a locally Noetherian algebraic space is coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
variable {F G : X.Modules}

/-- The tensor product of coherent modules on a locally Noetherian algebraic space is
coherent. -/
@[instance]
theorem isCoherent_tensor [F.IsCoherent] [G.IsCoherent] : (F ⊗ G).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
