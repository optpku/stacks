/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The projection from the test atlas to the ambient atlas. -/
def toInputAtlas : testAtlas X g ⟶ atlasScheme X :=
  (AtlasInput.representableEtale X).rep.fst' g

/-- The projection from the test atlas to the test scheme. -/
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

/-- The inclusion of the descended kernel-ideal subscheme into the test scheme. -/
def descendedInclusion : descendedScheme X Z g ⟶ T :=
  Over.homMk (localClosedToTest X Z g).imageι rfl

/-- The descended kernel-ideal subscheme is closed in the test scheme. -/
instance descendedInclusion_closed :
    AlgebraicGeometry.IsClosedImmersion (descendedInclusion X Z g).left := by
  change AlgebraicGeometry.IsClosedImmersion (localClosedToTest X Z g).imageι
  infer_instance

/-- The descended kernel-ideal subscheme maps into the image sheaf of the reduced atlas. -/
theorem descended_range :
    Subfunctor.range (yoneda.map (descendedInclusion X Z g) ≫ g) ≤
      (Subfunctor.range (chartMap X Z)).sheafify (Scheme.fppfTopology.over S) := by
  sorry

/-- The morphism to the image is literally the original X-value with the
proved membership attached; it preserves its specified map to X. -/
def descendedToImage : yoneda.obj (descendedScheme X Z g) ⟶ (imageSheaf X Z).obj :=
  Subfunctor.lift (yoneda.map (descendedInclusion X Z g) ≫ g) (descended_range X Z g)

/-- The descended map to the image sheaf has the prescribed composite into the ambient space. -/
theorem descended_commutes :
    descendedToImage X Z g ≫ (inclusion X Z).hom =
      yoneda.map (descendedInclusion X Z g) ≫ g :=
  Subfunctor.lift_ι _ _

/-- The fixed comparison into the actual presheaf fibre product. -/
def comparison : yoneda.obj (descendedScheme X Z g) ⟶ pullback (inclusion X Z).hom g :=
  pullback.lift (descendedToImage X Z g) (yoneda.map (descendedInclusion X Z g))
    (descended_commutes X Z g)

/-- The second pullback projection annihilates the ideal of the closed subscheme. -/
private theorem inverse_ker (U : (Over S)ᵒᵖ)
    (p : (pullback (inclusion X Z).hom g).obj U) :
    (descendedInclusion X Z g).left.ker ≤
      ((pullback.snd (inclusion X Z).hom g).app U p).left.ker := by
  sorry

/-- Lift the second pullback projection through the closed subscheme. -/
private def inverseApp (U : (Over S)ᵒᵖ)
    (p : (pullback (inclusion X Z).hom g).obj U) : U.unop ⟶ descendedScheme X Z g := by
  let j := (descendedInclusion X Z g).left
  let q := (pullback.snd (inclusion X Z).hom g).app U p
  let hClosed : AlgebraicGeometry.IsClosedImmersion j :=
    descendedInclusion_closed X Z g
  exact Over.homMk
    (@AlgebraicGeometry.IsClosedImmersion.lift _ _ _ j q.left hClosed
      (inverse_ker X Z g U p)) (by
        change (@AlgebraicGeometry.IsClosedImmersion.lift _ _ _ j q.left hClosed
          (inverse_ker X Z g U p)) ≫ (j ≫ T.hom) = U.unop.hom
        rw [← Category.assoc,
          @AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _ j q.left hClosed
            (inverse_ker X Z g U p)]
        exact Over.w q)

/-- The closed-subscheme lifts commute with restriction along test morphisms. -/
private theorem inverse_naturality {U V : (Over S)ᵒᵖ} (f : U ⟶ V) :
    (pullback (inclusion X Z).hom g).map f ≫ TypeCat.ofHom (inverseApp X Z g V) =
      TypeCat.ofHom (inverseApp X Z g U) ≫ (yoneda.obj (descendedScheme X Z g)).map f := by
  sorry

/-- The inverse comparison lifts the second projection through the closed subscheme. -/
@[no_expose] def comparisonInverse : pullback (inclusion X Z).hom g ⟶ yoneda.obj (descendedScheme X Z g) where
  app U := TypeCat.ofHom (inverseApp X Z g U)
  naturality _ _ f := private inverse_naturality X Z g f

/-- The comparison followed by its explicit inverse is the identity. -/
theorem comparison_comp_inverse :
    comparison X Z g ≫ comparisonInverse X Z g = 𝟙 (yoneda.obj (descendedScheme X Z g)) := by
  sorry

/-- The explicit inverse followed by the comparison is the identity. -/
theorem inverse_comp_comparison :
    comparisonInverse X Z g ≫ comparison X Z g = 𝟙 (pullback (inclusion X Z).hom g) := by
  sorry

/-- The closed subscheme represents the image-sheaf pullback via the two explicit comparisons. -/
def comparisonIso : yoneda.obj (descendedScheme X Z g) ≅ pullback (inclusion X Z).hom g where
  hom := comparison X Z g
  inv := comparisonInverse X Z g
  hom_inv_id := comparison_comp_inverse X Z g
  inv_hom_id := inverse_comp_comparison X Z g

/-- The canonical comparison to the image-sheaf pullback is an isomorphism. -/
instance comparison_isIso : IsIso (comparison X Z g) :=
  (comparisonIso X Z g).isIso_hom

/-- The descended closed subscheme represents the image-sheaf pullback to the test scheme. -/
theorem descended_isPullback :
    IsPullback (descendedToImage X Z g) (yoneda.map (descendedInclusion X Z g))
      (inclusion X Z).hom g :=
  IsPullback.of_iso_pullback ⟨descended_commutes X Z g⟩ (comparisonIso X Z g)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The inclusion of the image sheaf into the ambient algebraic space is representable. -/
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

/-- The inclusion of the reduced image algebraic space is a closed immersion. -/
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

