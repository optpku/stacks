module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport.Admissible

/-!
# Admissible finite supports on a base change

The small preorder of locally closed subsets of `|X_V|` whose reduced induced
scheme is finite over `V`, together with an ambient open in which the subset is
closed. This is the index category of `colim_Z H_Z(F)`.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace FiniteSupport

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f]

variable (V : Y.Etale)

/- Admissible finite supports on a base change. -/
#check (AlgebraicGeometry.Scheme.Etale.FiniteSupport.Admissible f V : Type u)

#check (AlgebraicGeometry.Scheme.Etale.FiniteSupport.Admissible.toIndexEquiv f V :
  Admissible f V ≃ FiniteSupportColimit.Index f V)

end FiniteSupport
end AlgebraicGeometry.Scheme.Etale

end
