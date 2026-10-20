/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A quasi-coherent module on the source of a quasi-compact immersion is isomorphic
to the pullback of a quasi-coherent module on the target. -/
theorem exists_quasiCoherentExtension_of_isImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsImmersion j] [QuasiCompact j] (G : U.Modules) [G.IsQuasicoherent] :
    ∃ H : X.Modules, H.IsQuasicoherent ∧ Nonempty ((pullback j).obj H ≅ G) := sorry

/-- A coherent module on an open subscheme of a Noetherian scheme is isomorphic
to the restriction of a coherent module on the scheme. -/
theorem exists_coherentExtension {X : Scheme.{u}} [IsNoetherian X] (U : X.Opens)
    (G : (U : Scheme).Modules) [G.IsCoherent] :
    ∃ H : X.Modules, H.IsCoherent ∧ Nonempty (H.restrict U.ι ≅ G) := sorry

end AlgebraicGeometry.Scheme.Modules
