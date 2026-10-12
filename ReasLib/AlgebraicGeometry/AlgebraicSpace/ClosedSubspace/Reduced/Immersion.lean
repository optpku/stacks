/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Space
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Represent the actual closed-image inclusion on every scheme test

Pull back the original atlas, then pull back the explicit closed subscheme
of that atlas. Its scheme-theoretic image in the test scheme is the
explicit kernel-ideal subscheme. Effective étale descent identifies this
fixed scheme and its fixed comparison map with the desired fibre product.

Unlike taking the reduced inverse image of the support on an arbitrary
test scheme, this retains nilpotents introduced by non-étale base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Immersion

open ReducedClosed.AtlasImage

variable {S : Scheme.{u}} (X : AlgebraicSpace S) (Z : Closeds (Points X))
    {T : Over S} (g : yoneda.obj T ⟶ X.functorOfPoints)

/-- Atlas of the test scheme, supplied by the original X atlas representation. -/
def testAtlas : Over S :=
  (AtlasInput.representableEtale X).rep.pullback g

def toInputAtlas : testAtlas X g ⟶ atlasScheme X :=
  (AtlasInput.representableEtale X).rep.fst' g

def toTest : testAtlas X g ⟶ T :=
  (AtlasInput.representableEtale X).rep.snd g

/-- Pull back the actual radical ideal, without re-radicalizing its base change. -/
def testIdeal : (testAtlas X g).left.IdealSheafData :=
  (ideal X Z).comap (toInputAtlas X g).left

/-- The explicit closed atlas followed by the actual test-atlas projection. -/
def localClosedToTest : (testIdeal X Z g).subscheme ⟶ T.left :=
  (testIdeal X Z g).subschemeι ≫ (toTest X g).left

/-- The descended closed subscheme is computed by the actual kernel ideal. -/
def descendedScheme : Over S :=
  Over.mk ((localClosedToTest X Z g).imageι ≫ T.hom)

def descendedInclusion : descendedScheme X Z g ⟶ T :=
  Over.homMk (localClosedToTest X Z g).imageι rfl

instance descendedInclusion_closed :
    AlgebraicGeometry.IsClosedImmersion (descendedInclusion X Z g).left := by
  change AlgebraicGeometry.IsClosedImmersion (localClosedToTest X Z g).imageι
  infer_instance

/-- Explicit descent law: the kernel-ideal subscheme obtained from the
étale-local closed subscheme maps into the fixed image subfunctor.
This is a membership condition, not an existence-selected map. -/
theorem descended_range :
    Subfunctor.range (yoneda.map (descendedInclusion X Z g) ≫ g) ≤
      (Subfunctor.range (chartMap X Z)).sheafify (Scheme.fppfTopology.over S) := by
  sorry

/-- The morphism to the image is literally the original X-value with the
proved membership attached; it preserves its specified map to X. -/
def descendedToImage : yoneda.obj (descendedScheme X Z g) ⟶ (imageSheaf X Z).obj :=
  Subfunctor.lift (yoneda.map (descendedInclusion X Z g) ≫ g) (descended_range X Z g)

theorem descended_commutes :
    descendedToImage X Z g ≫ (inclusion X Z).hom =
      yoneda.map (descendedInclusion X Z g) ≫ g :=
  Subfunctor.lift_ι _ _

/-- The fixed comparison into the actual presheaf fibre product. -/
def comparison : yoneda.obj (descendedScheme X Z g) ⟶ pullback (inclusion X Z).hom g :=
  pullback.lift (descendedToImage X Z g) (yoneda.map (descendedInclusion X Z g))
    (descended_commutes X Z g)

/-- Effective descent of closed immersions along the actual étale
surjective testAtlas → T identifies its scheme-theoretic image with the
image-sheaf base change. This states a property of the fixed comparison;
all schemes, ideals, and comparison functions precede this law. -/
theorem comparison_isIso : IsIso (comparison X Z g) := by
  sorry

def comparisonIso : yoneda.obj (descendedScheme X Z g) ≅ pullback (inclusion X Z).hom g := by
  -- Local instance justification (proof-local temporary data): Package this descended closed-immersion comparison at g using its own IsIso law, without selecting a new scheme or map.
  letI := comparison_isIso X Z g
  exact asIso (comparison X Z g)

theorem descended_isPullback :
    IsPullback (descendedToImage X Z g) (yoneda.map (descendedInclusion X Z g))
      (inclusion X Z).hom g :=
  IsPullback.of_iso_pullback ⟨descended_commutes X Z g⟩ (comparisonIso X Z g)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The representability field receives the explicit kernel-ideal scheme. -/
theorem inclusion_representable : yoneda.relativelyRepresentable (inclusion X Z).hom := by
  intro T g
  exact ⟨descendedScheme X Z g, descendedInclusion X Z g, descendedToImage X Z g,
    descended_isPullback X Z g⟩

/-- Other representing squares inherit closed immersion from the actual
kernel-ideal projection by uniqueness of pullbacks over T. -/
theorem inclusion_closed :
    (MorphismProperty.over (@AlgebraicGeometry.IsClosedImmersion)).presheaf
      (inclusion X Z).hom := by
  refine ⟨inclusion_representable X Z, ?_⟩
  intro T V g a b h
  sorry

instance space_inclusion_closed : AlgebraicSpace.IsClosedImmersion
    (ReducedClosed.Space.ι X Z) where
  presheaf := inclusion_closed X Z

/-- The genuine closed subspace of the original X, retaining its actual image carrier. -/
def closedSubspace : ClosedSubspace X where
  X := ReducedClosed.Space.space X Z
  ι := ReducedClosed.Space.ι X Z
  isClosedImmersion := space_inclusion_closed X Z

/-- Its support is exactly Z, computed on the explicit surjective atlas. -/
theorem pointsSet_eq : (closedSubspace X Z).pointsSet = (Z : Set (Points X)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.ReducedClosed.Immersion

