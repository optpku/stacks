/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Isomorphism
public import ReasLib.Algebra.Homology.DifferentialGradedModule.KFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism Transport for K-Flat Differential Graded Modules

The forgetful functor sends an isomorphism of differential graded modules to an isomorphism
of their underlying cochain complexes.  Consequently DGM K-flatness and its object property
are invariant under isomorphism.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R}

namespace IsKFlat

/-- K-flatness transports from the source to the target of an isomorphism of differential
graded modules; on underlying complexes the isomorphism is `(forgetToComplex A).mapIso e`. -/
theorem of_iso {M N : DifferentialGradedModule.{u, v} A}
    (hM : M.IsKFlat) (e : M ≅ N) : N.IsKFlat := sorry

/-- Isomorphic differential graded modules are simultaneously K-flat over the ground ring. -/
theorem iff_of_iso {M N : DifferentialGradedModule.{u, v} A} (e : M ≅ N) :
    M.IsKFlat ↔ N.IsKFlat := sorry

end IsKFlat

/-- The object property of K-flat differential graded modules is closed under isomorphisms. -/
@[stacks 06XZ "isomorphism stability of K-flat differential graded modules"]
instance kFlatIsClosedUnderIsomorphisms :
    (kFlat (A := A)).IsClosedUnderIsomorphisms := sorry

#synth (kFlat (A := A)).IsClosedUnderIsomorphisms

end DifferentialGradedModule
