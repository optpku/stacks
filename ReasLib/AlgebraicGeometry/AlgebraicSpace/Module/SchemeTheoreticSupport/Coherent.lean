/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian

/-!
# Coherent modules on scheme-theoretic supports

A coherent module on a locally Noetherian algebraic space is the pushforward of a
coherent module from any scheme-theoretic support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A quasi-coherent module on a scheme-theoretic support in a locally Noetherian
algebraic space whose pushforward is isomorphic to a coherent module is itself coherent. -/
theorem isCoherent_of_pushforward_iso {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] (G : Z.Modules) [G.IsQuasicoherent]
    (e : (pushforward i).obj G ≅ F) : G.IsCoherent :=
  sorry

namespace IsSchemeTheoreticSupport

/-- A coherent module on a locally Noetherian algebraic space is the pushforward of
a coherent module from any scheme-theoretic support. -/
theorem exists_coherent_module {S : Scheme.{u}} {X Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X)
    [IsSchemeTheoreticSupport F i] :
    ∃ G : Z.Modules, G.IsCoherent ∧ Nonempty ((pushforward i).obj G ≅ F) :=
  sorry

end IsSchemeTheoreticSupport

end AlgebraicGeometry.AlgebraicSpace.Modules
