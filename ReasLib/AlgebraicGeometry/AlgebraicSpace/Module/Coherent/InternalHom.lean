module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-!
# Internal Hom of coherent modules on algebraic spaces

The internal Hom of coherent modules on a locally Noetherian algebraic space is coherent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
variable {F G : X.Modules}

/-- The internal Hom of coherent modules on a locally Noetherian algebraic space is
coherent. -/
@[instance]
theorem isCoherent_internalHom [F.IsCoherent] [G.IsCoherent] :
    (internalHom F G).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
