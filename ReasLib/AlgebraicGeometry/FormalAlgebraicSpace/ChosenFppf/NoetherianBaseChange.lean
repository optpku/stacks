module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.NoetherianLocalMorphismProperty
public import ReasLib.RingTheory.Topology.Noetherian.BaseChange

/-!
# Relative base change of local properties of locally Noetherian formal algebraic spaces

Stability of local ring-morphism properties under completed base change
transfers affine étale local tests to pullback projections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P Q : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [IsLocallyNoetherian Z]

/-- If local ring-morphism properties `P` and `Q` satisfy stability of `P` under
base change by `Q`, then the second projection of a pullback satisfies the
affine étale local test for `P` whenever its two input morphisms satisfy
the tests for `P` and `Q`, respectively. -/
theorem etaleAffineLocally.pullback_snd_of_stableUnderBaseChangeBy
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) (hg : etaleAffineLocally Q g) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- For a pullback square of locally Noetherian formal algebraic spaces, the
base-change leg satisfies the affine étale local test for `P` if the input
legs satisfy the tests for `P` and `Q` and `P` is stable under base change by `Q`. -/
theorem etaleAffineLocally.of_isPullback_of_stableUnderBaseChangeBy
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f)
    (hg : etaleAffineLocally Q g) :
    etaleAffineLocally P snd := sorry

/-- If local ring-morphism properties `P` and `Q` satisfy stability of `P` under
base change by `Q`, the second pullback projection satisfies the target-cover
test for `P` whenever the input morphisms satisfy the tests for `P` and `Q`. -/
theorem existsCoverOnTarget.pullback_snd_of_stableUnderBaseChangeBy
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) (hg : existsCoverOnTarget Q g) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- If local ring-morphism properties `P` and `Q` satisfy stability of `P` under
base change by `Q`, the second pullback projection satisfies the source-cover
test for `P` whenever the input morphisms satisfy the tests for `P` and `Q`. -/
theorem existsCoverOnSource.pullback_snd_of_stableUnderBaseChangeBy
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hQ : Noetherian.IsLocalMorphismProperty Q)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChangeBy P Q)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) (hg : existsCoverOnSource Q g) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

namespace AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable (P : ∀ {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B],
    (B →+* A) → Prop)
variable {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable [IsLocallyNoetherian Z]

/-- On a size-closed chosen big fppf site, a local morphism property of
Noetherian adic rings stable under completed base change induces an affine
étale local test preserved by pullback of locally Noetherian formal algebraic
spaces. -/
theorem etaleAffineLocally.pullback_snd
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : etaleAffineLocally P f) :
    etaleAffineLocally P (pullback.snd f g) := sorry

/-- If `IsPullback fst snd f g` and `f` satisfies `etaleAffineLocally P`, then
the base-change leg `snd` satisfies `etaleAffineLocally P`. -/
theorem etaleAffineLocally.of_isPullback
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    {W : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsLocallyNoetherian W]
    {f : X ⟶ Y} {g : Z ⟶ Y} {fst : W ⟶ X} {snd : W ⟶ Z}
    (sq : IsPullback fst snd f g) (hf : etaleAffineLocally P f) :
    etaleAffineLocally P snd := sorry

/-- On a size-closed chosen big fppf site, the target-cover test of a local
Noetherian adic ring morphism property stable under completed base change is
preserved by pullback of locally Noetherian formal algebraic spaces. -/
theorem existsCoverOnTarget.pullback_snd
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnTarget P f) :
    existsCoverOnTarget P (pullback.snd f g) := sorry

/-- On a size-closed chosen big fppf site, the source-cover test of a local
Noetherian adic ring morphism property stable under completed base change is
preserved by pullback of locally Noetherian formal algebraic spaces. -/
theorem existsCoverOnSource.pullback_snd
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (hP : Noetherian.IsLocalMorphismProperty P)
    (hbc : Noetherian.IsLocalMorphismProperty.IsStableUnderBaseChange P)
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g]
    (hf : existsCoverOnSource P f) :
    existsCoverOnSource P (pullback.snd f g) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
