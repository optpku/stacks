/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Faithfulness of small étale ringed topoi of algebraic spaces

Two morphisms of algebraic spaces over a scheme that induce `2`-isomorphic morphisms of
small étale ringed topoi are equal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Two morphisms of algebraic spaces over a scheme are equal if their canonical morphisms
of small étale ringed topoi admit a `2`-isomorphism compatible with the structure-sheaf maps. -/
theorem eq_of_smallEtaleRingedTopos_twoIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {a b : X ⟶ Y} (h : Nonempty (RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (ringedToposHom a) (ringedToposHom b))) :
    a = b := sorry

end AlgebraicGeometry.AlgebraicSpace
