/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent

/-!
# Coherence of pulled-back scheme modules

Pullback along a morphism of locally Noetherian schemes preserves coherence of module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback along a morphism of locally Noetherian schemes preserves coherence of module
sheaves. -/
instance pullback_isCoherent {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (G : Y.Modules) [G.IsCoherent] :
    ((Scheme.Modules.pullback f).obj G).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
