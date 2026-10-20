/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-! # Represented pullbacks of representable morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The projection to the source space from the scheme representing a pullback along a scheme. -/
def representablePullbackFst {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {V : Over S} (g : ofOver V ⟶ Y) : ofOver (hf.pullback g) ⟶ X :=
  hf.fst g

/-- The projection to the base scheme from the scheme representing a pullback. -/
def representablePullbackSnd {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {V : Over S} (g : ofOver V ⟶ Y) :
    ofOver (hf.pullback g) ⟶ ofOver V :=
  ofOverMap (hf.snd g)

/-- The represented projections form a cartesian square of algebraic spaces. -/
theorem representablePullback_isPullback {f : X ⟶ Y} (hf : yoneda.relativelyRepresentable f)
    {V : Over S} (g : ofOver V ⟶ Y) :
    IsPullback (representablePullbackFst hf g) (representablePullbackSnd hf g) f g :=
  sorry

/-- The projection to the source space is étale when the morphism from the base scheme is étale. -/
instance instEtaleRepresentablePullbackFst {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f) {V : Over S} (g : ofOver V ⟶ Y) [Etale g] :
    Etale (representablePullbackFst hf g) :=
  Etale.of_isPullback (representablePullback_isPullback hf g).flip inferInstance

end AlgebraicGeometry.AlgebraicSpace.Modules
