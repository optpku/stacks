module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InternalHom.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coherence of internal Hom on locally Noetherian schemes

Internal Hom of coherent modules on a locally Noetherian scheme is coherent.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable {F G : X.Modules}
variable [IsLocallyNoetherian X]

/-- Internal Hom of coherent modules on a locally Noetherian scheme is coherent. -/
@[stacks 01Y2, instance]
theorem isCoherent_internalHom
    [F.IsCoherent] [G.IsCoherent] :
    ((ihom F).obj G).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
