/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

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

/-- Let `f : Y ⟶ X` be a quasi-compact, quasi-separated, flat, surjective morphism of locally
Noetherian algebraic spaces over a scheme. If `F` and `G` are quasi-coherent modules on `X`
and `Y`, respectively, `G` is coherent, and `φ : G ⟶ (pullback f).obj F` is injective, then
the pullback `F ∩ f_* G` of the adjunction unit along `f_* φ` is coherent. -/
@[stacks 0GPR, instance]
theorem isCoherent_intersectPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [Flat f] [Surjective f]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {F : X.Modules} {G : Y.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] [G.IsCoherent]
    (φ : G ⟶ (pullback f).obj F) [Mono φ] :
    (intersectPushforward f φ).IsCoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
