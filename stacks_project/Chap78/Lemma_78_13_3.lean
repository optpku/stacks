/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Intersection
import StacksCheckRecall

/-!
# Coherence of the intersection with a pushforward

For a quasi-compact, quasi-separated, flat, surjective morphism of locally Noetherian
algebraic spaces, intersecting a quasi-coherent module with the pushforward of a coherent
submodule of its pullback gives a coherent module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 78.13.3: Let `S` be a scheme, and let `f : Y ⟶ X` be a morphism of algebraic spaces
over `S`. Let `F` be a quasi-coherent `𝒪_X`-module, let `G` be a quasi-coherent `𝒪_Y`-module,
and let `φ : G ⟶ (pullback f).obj F` be an injective module map. If `f` is quasi-compact,
quasi-separated, flat, and surjective, `X` and `Y` are locally Noetherian, and `G` is coherent,
then `F ∩ f_* G`, defined as the pullback of the adjunction unit `F ⟶ f_* f^* F` along `f_* φ`,
is a coherent `𝒪_X`-module. -/
@[stacks 0GPR] #check (AlgebraicGeometry.AlgebraicSpace.Modules.isCoherent_intersectPushforward :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [Flat f] [Surjective f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {F : X.Modules} {G : Y.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsCoherent]
    (φ : G ⟶ (pullback f).obj F) [Mono φ],
    (intersectPushforward f φ).IsCoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
