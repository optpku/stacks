/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Jacobson
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.6.3: a scheme is Jacobson exactly when it is locally Jacobson, when every affine-open
section ring is Jacobson, when this holds on one affine open cover, or when it has an open cover by
Jacobson open subschemes. -/
@[stacks 01P4] #check
  (AlgebraicGeometry.Scheme.jacobsonSpace_tfae :
    ∀ (X : Scheme.{u}),
      List.TFAE [
        JacobsonSpace X,
        X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsJacobsonRing A),
        ∀ U : X.affineOpens, IsJacobsonRing Γ(X, U),
        ∃ 𝒰 : X.AffineOpenCover,
          ∀ i : 𝒰.I₀, IsJacobsonRing Γ(X, (𝒰.f i).opensRange),
        ∃ 𝒰 : X.OpenCover,
          ∀ i : 𝒰.I₀, JacobsonSpace ((𝒰.f i).opensRange).toScheme])

#check
  (AlgebraicGeometry.Scheme.jacobsonSpace_toScheme :
    ∀ (X : Scheme.{u}) (_ : JacobsonSpace X) (U : X.Opens),
      JacobsonSpace U.toScheme)
