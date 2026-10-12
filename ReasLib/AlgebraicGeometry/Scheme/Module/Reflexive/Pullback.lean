/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import ReasLib.Algebra.Module.Reflexive
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive

/-!
# Reflexivity of pulled-back scheme modules

Flat pullback between integral locally Noetherian schemes preserves reflexive coherent module
sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Flat pullback between integral locally Noetherian schemes preserves reflexivity of coherent
module sheaves. -/
instance pullback_isReflexive_of_flat {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [Flat f] (G : Y.Modules) [G.IsCoherent] [IsReflexive G] :
    IsReflexive ((Scheme.Modules.pullback f).obj G) := sorry

end AlgebraicGeometry.Scheme.Modules
