/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.Products
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

/-!
# Relative finite presentation and biproducts

Relative finite presentation passes from a binary biproduct of quasicoherent scheme modules to
both direct summands.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver

variable {X S : Scheme.{u}}

/-- Relative finite presentation of a binary biproduct of quasicoherent scheme modules implies
relative finite presentation of both direct summands. -/
theorem summands_of_biprod (f : X ⟶ S) [LocallyOfFiniteType f]
    (F F' : X.Modules) [F.IsQuasicoherent] [F'.IsQuasicoherent]
    (h : (F ⊞ F').IsFinitePresentationOver f) :
    F.IsFinitePresentationOver f ∧ F'.IsFinitePresentationOver f := sorry

end AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver
