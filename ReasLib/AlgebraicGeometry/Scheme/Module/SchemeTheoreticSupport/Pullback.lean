/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.SchemeTheoreticSupport
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.Algebra.Module.Torsion.BaseChange
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Scheme-theoretic support under pullback

This leaf records preservation of the annihilator-defined scheme-theoretic support of a
finite-type quasicoherent module under flat pullback.
-/

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Modules
namespace IsSchemeTheoreticSupport

/-- Flat pullback carries a scheme-theoretic support of a finite-type quasicoherent module
to the pulled-back ideal-sheaf datum. -/
@[stacks 07T9]
theorem pullback_of_flat {X Y : Scheme.{u}}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (I : X.IdealSheafData) (hI : IsSchemeTheoreticSupport ℱ I)
    (f : Y ⟶ X) [Flat f] :
    IsSchemeTheoreticSupport ((Scheme.Modules.pullback f).obj ℱ) (I.comap f) := sorry

end IsSchemeTheoreticSupport
end Scheme.Modules
end AlgebraicGeometry

end
