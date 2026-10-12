/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Integral pushforwards of structure sheaves

This file records when the pushforward of a structure sheaf is integral as a
quasi-coherent algebra over the target scheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X S : Scheme.{u}}

/-- The pushed-forward structure sheaf of a quasi-compact, quasi-separated,
universally closed morphism is integral as a quasi-coherent algebra over the target. -/
theorem pushforwardStructureSheafQcAlgebra_isIntegral_of_universallyClosed
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] :
    (pushforwardStructureSheafQcAlgebra f).IsIntegral := sorry

end AlgebraicGeometry.Scheme
