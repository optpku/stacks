/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeTheoreticSupport.Coherent

/-!
# Coherent modules on scheme-theoretic supports

A coherent module on a locally Noetherian algebraic space is the pushforward of a
coherent module from any scheme-theoretic support. Closed immersions into locally
Noetherian algebraic spaces have locally Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian.of_isClosedImmersion :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i], IsLocallyNoetherian Z)

#check (AlgebraicGeometry.AlgebraicSpace.instIsLocallyNoetherian_of_isClosedImmersion :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (Z : ClosedSubspace X), IsLocallyNoetherian Z.X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_of_pushforward_iso :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X) [Modules.IsSchemeTheoreticSupport F i]
    (G : Z.Modules) [G.IsQuasicoherent] (e : (Modules.pushforward i).obj G ≅ F),
    G.IsCoherent)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.IsSchemeTheoreticSupport.exists_coherent_module :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (i : Z ⟶ X) [Modules.IsSchemeTheoreticSupport F i],
    ∃ G : Z.Modules, G.IsCoherent ∧ Nonempty ((Modules.pushforward i).obj G ≅ F))
