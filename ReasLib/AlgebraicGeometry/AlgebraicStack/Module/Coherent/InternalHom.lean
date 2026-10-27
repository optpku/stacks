/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom.FinitePresentation

/-!
# Coherence of internal Hom on locally Noetherian algebraic stacks

On a locally Noetherian algebraic stack, the internal Hom of coherent
`𝒪_X`-modules constructed as `QCoh.internalHomFP` is again coherent.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Internal Hom of coherent `𝒪_X`-modules on a locally Noetherian algebraic stack
is coherent. -/
@[instance]
theorem isCoherent_internalHomFP {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] {F : fppfModules X} {G : QCoh X}
    [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G.obj] :
    AlgebraicStack.IsCoherent (QCoh.internalHomFP F G).obj := sorry

end AlgebraicGeometry.AlgebraicStack
