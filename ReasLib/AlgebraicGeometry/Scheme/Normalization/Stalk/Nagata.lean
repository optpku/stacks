module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Basic

@[expose] public section

/-!
# Nagata normalization stalks

This leaf supplies the Nagata-ring instance at a scheme stalk required by
local normalization and completion arguments.
-/

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Stalk

variable (X : Scheme.{u}) [Nagata X]
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- A stalk of a Nagata scheme is a Nagata ring. -/
instance instNagataRing (x : X) :
    NagataRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme.Normalization.Stalk
