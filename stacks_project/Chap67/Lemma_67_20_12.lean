/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Artinian
import StacksCheckRecall

/-!
# Morphisms from Artinian spectra to quasi-separated algebraic spaces

Any morphism from the spectrum of an Artinian ring to a quasi-separated algebraic
space is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.20.12: Let `S` be a scheme. Let `X` be a quasi-separated algebraic
space over `S`, meaning `X` is absolutely quasi-separated via `toSpecZ`.
Let `A` be an Artinian ring. Any morphism `Spec (.of A) ⟶ X` of algebraic
spaces over `S` is affine. -/
@[stacks 09TF] #check (AlgebraicGeometry.AlgebraicSpace.Affine.of_artinianSpec :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiSeparated (toSpecZ X)] {A : Type u} [CommRing A] [IsArtinianRing A]
    {σ : Spec (.of A) ⟶ S} (f : ofOver (Over.mk σ) ⟶ X), Affine f)

end AlgebraicGeometry.AlgebraicSpace
