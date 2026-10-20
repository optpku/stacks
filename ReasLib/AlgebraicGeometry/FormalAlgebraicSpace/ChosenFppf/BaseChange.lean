/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.TypesPullback
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.BaseChange

/-!
# Base change of local properties of formal algebraic space morphisms

Local properties of morphisms of countably indexed weakly admissible rings
stable under completed base change induce pullback-stable affine étale local
and covering tests on locally countably indexed formal algebraic spaces over
a size-closed chosen big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B] [IsCountablyIndexed B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
variable [IsLocallyCountablyIndexed Z]

/-- On a size-closed chosen big fppf site, a local property of morphisms of
countably indexed weakly admissible rings stable under completed base change
induces an affine étale local test preserved by pullback of locally countably
indexed formal algebraic spaces. -/
theorem etaleAffineLocally.pullback_snd
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- If `IsPullback fst snd f g` and `f` satisfies `etaleAffineLocally P`, then
the base-change leg `snd` satisfies `etaleAffineLocally P`. -/
theorem etaleAffineLocally.of_isPullback
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyCountablyIndexed W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f) :
    etaleAffineLocally P snd := sorry

/-- On a size-closed chosen big fppf site, the target-cover test of a local
property of morphisms of countably indexed weakly admissible rings stable
under completed base change is preserved by pullback of locally countably
indexed formal algebraic spaces. -/
theorem existsCoverOnTarget.pullback_snd
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- On a size-closed chosen big fppf site, the source-cover test of a local
property of morphisms of countably indexed weakly admissible rings stable
under completed base change is preserved by pullback of locally countably
indexed formal algebraic spaces. -/
theorem existsCoverOnSource.pullback_snd
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : IsLocalMorphismProperty P)
    (hbc : IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsLocallyCountablyIndexed
