/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.J2.Locality
import StacksCheckRecall

open scoped AlgebraicGeometry

universe u

/- Lemma 29.19.2 (1): for a locally Noetherian scheme, being J-2 is equivalent to being J-2
on an open cover, to all affine-open section rings being J-2, and to this ring condition holding
on an affine open cover. -/
@[stacks 07R4] #check
  (AlgebraicGeometry.Scheme.isJ2_tfae :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X],
      List.TFAE [
        AlgebraicGeometry.Scheme.IsJ2 X,
        ∃ 𝒰 : X.OpenCover,
          ∀ i : 𝒰.I₀, AlgebraicGeometry.Scheme.IsJ2 (𝒰.X i),
        ∀ U : X.affineOpens,
          IsJ2Ring.{u, u} (Γ(X, (U : X.Opens))),
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀, IsJ2Ring.{u, u} (Γ(X, (𝒰.f i).opensRange))
      ])

/- Lemma 29.19.2 (2): every scheme locally of finite type over a J-2 scheme is J-2. -/
@[stacks 07R4] #check
  (AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.Scheme.IsJ2 X] [AlgebraicGeometry.LocallyOfFiniteType f],
      AlgebraicGeometry.Scheme.IsJ2 Y)
