/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-! # Pushforward along representable morphisms and restriction to a scheme atlas -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- For a representable quasi-compact quasi-separated morphism and an étale surjective scheme
atlas of its target, restriction of the pushforward of a quasi-coherent module is canonically
isomorphic to pushforward of its restriction to the represented pullback. -/
def representablePushforwardIso {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    (F : X.Modules) [F.IsQuasicoherent] :
    (restrictFunctor g).obj ((pushforward f).obj F) ≅
      (pushforward (representablePullbackSnd hf g)).obj
        (restrict F (representablePullbackFst hf g)) :=
  pushforwardEtaleBaseChangeIso (representablePullback_isPullback hf g) F

/-- The forward map of the represented pushforward identification is the canonical comparison. -/
theorem representablePushforwardIso_spec {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    [QuasiCompact f] [QuasiSeparated f] {V : Over S} (g : ofOver V ⟶ Y)
    [Etale g] [Surjective g]
    (F : X.Modules) [F.IsQuasicoherent] :
    (representablePushforwardIso hf g F).hom =
      pushforwardEtaleBaseChangeHom (representablePullback_isPullback hf g) F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
