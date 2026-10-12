/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism

/-!
# Scheme-theoretic images of reduced algebraic spaces

If `X` is reduced, a scheme-theoretic image factorization of `f : X ⟶ Y` is
the reduced induced algebraic space structure on the closure of the set of
points `|f|(|X|)`. Formation of this image commutes with étale base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The closure of the set of points `|f|(|X|)` in a topology on `|Y|`. -/
def rangeClosure {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (τY : TopologicalSpace (Points Y)) : Set (Points Y) :=
  @closure (Points Y) τY (Set.range (Points.map f))

/-- `rangeClosure f τY` is the closure of `Set.range (Points.map f)` in `τY`. -/
theorem rangeClosure_def {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (τY : TopologicalSpace (Points Y)) :
    rangeClosure f τY = @closure (Points Y) τY (Set.range (Points.map f)) :=
  sorry

/-- The image of points of `f` is contained in `rangeClosure f τY`. -/
theorem subset_rangeClosure {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (τY : TopologicalSpace (Points Y)) :
    Set.range (Points.map f) ⊆ rangeClosure f τY :=
  sorry

namespace IsSchemeTheoreticImage

/-- If `X` is reduced, a scheme-theoretic image of `f : X ⟶ Y` is reduced. -/
theorem isReduced {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    {toImage : X ⟶ Z} {ι : Z ⟶ Y} [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] : IsReduced Z :=
  sorry

/-- If `X` is reduced, the points of a scheme-theoretic image of `f` are the
closure of `|f|(|X|)` in any canonical topology on `|Y|`. -/
theorem range_eq_rangeClosure {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    {f : X ⟶ Y} {toImage : X ⟶ Z} {ι : Z ⟶ Y} [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] {τY : TopologicalSpace (Points Y)}
    (hτ : IsPointsTopology Y τY) :
    Set.range (Points.map ι) = rangeClosure f τY :=
  sorry

/-- A closed-immersion factorization of a morphism from a reduced algebraic space
is a scheme-theoretic image if and only if the closed subspace is reduced and
its points are the closure of `|f|(|X|)`. This is the reduced induced algebraic
space structure on that closure. -/
theorem iff_isReduced_range_eq_rangeClosure {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced X] (f : X ⟶ Y) (toImage : X ⟶ Z)
    (ι : Z ⟶ Y) :
    IsSchemeTheoreticImage f toImage ι ↔
      toImage ≫ ι = f ∧ IsClosedImmersion ι ∧ IsReduced Z ∧
        ∀ (τY : TopologicalSpace (Points Y)), IsPointsTopology Y τY →
          Set.range (Points.map ι) = rangeClosure f τY :=
  sorry

/-- A reduced closed subspace of `Y` through which a morphism from a reduced
algebraic space factors, with points equal to `rangeClosure f τY` for every
canonical topology, is a scheme-theoretic image of `f`. -/
theorem of_isReduced_range_eq_rangeClosure {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} [IsReduced X] (f : X ⟶ Y) (toImage : X ⟶ Z)
    (ι : Z ⟶ Y) [IsClosedImmersion ι] [IsReduced Z] (hfac : toImage ≫ ι = f)
    (hsupport : ∀ (τY : TopologicalSpace (Points Y)), IsPointsTopology Y τY →
      Set.range (Points.map ι) = rangeClosure f τY) :
    IsSchemeTheoreticImage f toImage ι :=
  sorry

/-- The pair `(pullback.fst f φ ≫ toImage, pullback.snd f φ)` is compatible with
`ι` and `φ`. -/
theorem pullbackToImage_condition {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ] :
    (pullback.fst f φ ≫ toImage) ≫ ι = pullback.snd f φ ≫ φ :=
  sorry

/-- The comparison `X ×_Y V ⟶ Z ×_Y V` induced by a scheme-theoretic image
factorization of `f`, as a morphism of chosen pullbacks. -/
def pullbackToImage {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ]
    [HasPullback ι φ] : pullback f φ ⟶ pullback ι φ :=
  pullback.lift (pullback.fst f φ ≫ toImage) (pullback.snd f φ)
    (pullbackToImage_condition f toImage ι φ)

/-- `pullbackToImage f toImage ι φ` projects to `toImage` on the first factor. -/
theorem pullbackToImage_fst {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ]
    [HasPullback ι φ] :
    pullbackToImage f toImage ι φ ≫ pullback.fst ι φ =
      pullback.fst f φ ≫ toImage :=
  sorry

/-- `pullbackToImage f toImage ι φ` projects to `pullback.snd f φ` on the second
factor. -/
theorem pullbackToImage_snd {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ]
    [HasPullback ι φ] :
    pullbackToImage f toImage ι φ ≫ pullback.snd ι φ = pullback.snd f φ :=
  sorry

/-- Scheme-theoretic images of morphisms from reduced algebraic spaces commute
with étale base change, as a statement about chosen pullbacks. -/
theorem of_pullback_etale {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [Etale φ]
    [HasPullback f φ] [HasPullback ι φ] :
    IsSchemeTheoreticImage (pullback.snd f φ) (pullbackToImage f toImage ι φ)
      (pullback.snd ι φ) :=
  sorry

/-- The opposite compatibility used to lift into `inverseImage φ ι`. -/
theorem pullbackToInverseImage_condition {S : Scheme.{u}}
    {X Y Z V : AlgebraicSpace S} (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] (φ : V ⟶ Y) [HasPullback f φ] :
    pullback.snd f φ ≫ φ = (pullback.fst f φ ≫ toImage) ≫ ι :=
  sorry

/-- The comparison `X ×_Y V ⟶ Z ×_Y V` into the closed inverse image of `ι`
along an étale morphism `φ : V ⟶ Y`. -/
def pullbackToInverseImage {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [HasPullback f φ] : pullback f φ ⟶ inverseImage φ ι :=
  (inverseImage_isPullback φ ι).lift (pullback.snd f φ)
    (pullback.fst f φ ≫ toImage) (pullbackToInverseImage_condition f toImage ι φ)

/-- `pullbackToInverseImage f toImage ι φ` composes to `pullback.snd f φ` along
the closed inclusion of `inverseImage φ ι`. -/
theorem pullbackToInverseImage_ι {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [HasPullback f φ] :
    pullbackToInverseImage f toImage ι φ ≫ inverseImageι φ ι =
      pullback.snd f φ :=
  sorry

/-- `pullbackToInverseImage f toImage ι φ` composes to
`pullback.fst f φ ≫ toImage` along the comparison into `Z`. -/
theorem pullbackToInverseImage_to {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y)
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [HasPullback f φ] :
    pullbackToInverseImage f toImage ι φ ≫ inverseImageTo φ ι =
      pullback.fst f φ ≫ toImage :=
  sorry

/-- For an étale morphism `φ : V ⟶ Y`, the scheme-theoretic image of
`X ×_Y V ⟶ V` is the closed inverse image `Z ×_Y V`. -/
theorem of_inverseImage_etale {S : Scheme.{u}} {X Y Z V : AlgebraicSpace S}
    (f : X ⟶ Y) (toImage : X ⟶ Z) (ι : Z ⟶ Y) [IsReduced X]
    [IsSchemeTheoreticImage f toImage ι] [IsClosedImmersion ι] (φ : V ⟶ Y)
    [Etale φ] [HasPullback f φ] :
    IsSchemeTheoreticImage (pullback.snd f φ)
      (pullbackToInverseImage f toImage ι φ) (inverseImageι φ ι) :=
  sorry

end IsSchemeTheoreticImage

end AlgebraicGeometry.AlgebraicSpace
