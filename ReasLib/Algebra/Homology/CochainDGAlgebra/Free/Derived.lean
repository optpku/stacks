/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Free.Resolution
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.QuasiIso.Derived
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived equivalence attached to a free K-flat resolution

This leaf keeps the concrete resolution owner lightweight while exposing the canonical derived
equivalence attached to its quasi-isomorphic comparison map.
-/

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u v w

namespace CochainDGAlgebra.Free.KFlatResolution

variable {R : Type u} [CommRing R]
variable {B : CochainDGAlgebra.{u, v} R} (P : KFlatResolution.{u, v, w} B)

/-- The derived equivalence attached to a free K-flat resolution is the canonical equivalence
induced by its quasi-isomorphic comparison map. -/
@[stacks 09S6 "derived equivalence induced by a free K-flat resolution map"]
noncomputable def triangulatedEquivalence :
    RLinear.TriangulatedEquivalence R
      (DifferentialGradedModule.Derived.Category P.complex)
      (DifferentialGradedModule.Derived.Category B) :=
  CochainDGAlgebra.Hom.Derived.triangulatedEquivalence P.π P.quasiIso

/-- The forward functor of the resolution equivalence is derived extension of scalars. -/
@[simp, stacks 09S6 "forward functor of a free resolution equivalence"]
theorem triangulatedEquivalence_functor :
    P.triangulatedEquivalence.functor =
      CochainDGAlgebra.Hom.Derived.extension P.π := sorry

/-- The inverse functor of the resolution equivalence is derived restriction of scalars. -/
@[simp, stacks 09S6 "inverse functor of a free resolution equivalence"]
theorem triangulatedEquivalence_inverse :
    P.triangulatedEquivalence.inverse =
      CochainDGAlgebra.Hom.Derived.restriction P.π := sorry

end CochainDGAlgebra.Free.KFlatResolution
