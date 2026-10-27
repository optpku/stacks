/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.AssociatedPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.4.8: Let `S` be a local scheme with closed point `s`. Let
`f : X ⟶ S` be a morphism from an algebraic space `X` to `S` which is locally
of finite type. Let `ℱ` be a finite type quasi-coherent `𝒪_X`-module. Assume
that every point of `Ass_{X/S}(ℱ)` specializes to a point of the closed fibre
`X_s`, and that `ℱ` is flat over `S` at every point of `X_s`. Then `ℱ` is
flat over `S`.
Here `f` is `SchemeRealization.toBase X`, `Ass_{X/S}(ℱ)` is
`relativeAssassin (SchemeRealization.toBase X) ℱ`,
and `|X_s|` is `{z | Points.base z = s}`. The closed point is identified by
`S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤)`. Flatness over `S` is
the pointwise condition `flatOverAt ℱ (SchemeRealization.toBase X)`. The specialization
assumption holds, for example, if `f` is of finite type and `ℱ` is pure
along `X_s`, or if `f` is proper. -/
@[stacks 0CWM] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.relativeAssassin.flatOver_of_specializesTo_closedFiber :
    ∀ {S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)] {X : AlgebraicSpace S}
    [LocallyOfFiniteType (SchemeRealization.toBase X)] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (h_ass : ∀ x ∈ relativeAssassin (SchemeRealization.toBase X) ℱ,
      ∃ z : Points X, Points.base z = s ∧ Specializes x z)
    (h_flat : ∀ z : Points X, Points.base z = s →
      flatOverAt ℱ (SchemeRealization.toBase X) z),
    flatOver ℱ (SchemeRealization.toBase X))

end AlgebraicGeometry.AlgebraicSpace.Modules
