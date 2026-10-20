/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.Artinian
import StacksCheckRecall

/-!
# Lemma 85.31.3

A descent datum relative to a quasi-compact flat surjective morphism is effective
when the scheme in its single covering-family component is a disjoint union of
spectra of Artinian rings. The covering family has one component; its scheme need
not be connected.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

/- Lemma 85.31.3: A descent datum along a quasi-compact flat surjective morphism
is effective if its component scheme is a disjoint union of spectra of Artinian rings. -/
@[stacks 024I] #check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.of_sigma_artinianSpec :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [QuasiCompact f] [Flat f] [Surjective f]
      (D : Scheme.DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
      {I : Type u} (A : I → CommRingCat.{u}) [∀ i, IsArtinianRing (A i)]
      (e : (D.obj default).left ≅ ∐ fun i ↦ Spec (A i)),
      D.IsEffective)

#check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofIsLocallyArtinian :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [QuasiCompact f] [Flat f] [Surjective f]
      (D : Scheme.DescentData (fun _ : PUnit.{v + 1} ↦ X) (fun _ ↦ f))
      [IsLocallyArtinian (D.obj default).left],
      D.IsEffective)
