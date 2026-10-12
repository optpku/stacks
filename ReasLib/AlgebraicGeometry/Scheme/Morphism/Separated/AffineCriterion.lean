/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AffineOpenPair.Sections

/-!
# Affine criteria for separated scheme morphisms

The primary algebraic comparison is relative: it is the map from the pushout
of section rings over a common affine target.  The absolute tensor map over
`ℤ` is retained as an equivalent convenience interface.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- Lemma 26.21.7 (1): for a separated morphism, affine opens over a common affine target have
affine intersection. -/
@[stacks 01KP]
theorem Scheme.Hom.isAffineOpen_inter_of_isSeparated
    (f : X ⟶ S) [IsSeparated f] (U V : X.affineOpens)
    (hcommon : f.HasCommonAffineTarget U V) :
    IsAffineOpen ((U : X.Opens) ⊓ V) := sorry

/-- Lemma 26.21.7 (2): for a separated morphism, the absolute tensor comparison for affine opens
over a common affine target is surjective. -/
@[stacks 01KP]
theorem Scheme.Hom.sectionTensorToIntersection_surjective_of_isSeparated
    (f : X ⟶ S) [IsSeparated f] (U V : X.affineOpens)
    (hcommon : f.HasCommonAffineTarget U V) :
    Function.Surjective (X.sectionTensorToIntersection U V).hom := sorry

/-- For a separated morphism, the section comparison determined by common-affine-target data is
surjective. -/
@[stacks 01KP "relative sections comparison for a separated morphism"]
theorem Scheme.Hom.CommonAffineTarget.sectionsComparison_surjective
    {f : X ⟶ S} {U V : X.affineOpens}
    (W : f.CommonAffineTarget U V) [IsSeparated f] :
    Function.Surjective (W.sectionsComparison).hom := sorry

/-- For a separated morphism, the relative section-ring pushout over a common affine target
surjects onto sections of the intersection. This is the unbundled compatibility interface. -/
@[stacks 01KP "relative section-pushout surjectivity"]
theorem Scheme.Hom.sectionPushoutToIntersection_surjective_of_isSeparated
    (f : X ⟶ S) [IsSeparated f] (U V : X.affineOpens) (W : S.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ W) (hV : V ≤ f ⁻¹ᵁ W) :
    Function.Surjective
      (f.sectionPushoutToIntersection U V W hU hV).hom := sorry

/- The iff forms expose both directions of the source-facing characterization while retaining the
fine-grained implication below for callers that already have the neighborhood data. -/

/-- 01KP, Lemma 26.21.7 (3): separatedness is equivalent to the absolute affine-neighborhood criterion
with surjective section-tensor comparison. -/
@[stacks 01KP "absolute affine-neighborhood characterization"]
theorem Scheme.Hom.isSeparated_iff_exists_affineNeighborhoods
    (f : X ⟶ S) :
    IsSeparated f ↔
      (∀ (x1 x2 : X), f.base x1 = f.base x2 →
        ∃ U V : X.affineOpens,
          x1 ∈ (U : X.Opens) ∧ x2 ∈ (V : X.Opens) ∧
            f.HasCommonAffineTarget U V ∧
              IsAffineOpen ((U : X.Opens) ⊓ V) ∧
                Function.Surjective (X.sectionTensorToIntersection U V).hom) := sorry

/-- 01KP: the relative common-target pushout form of the separatedness characterization. -/
@[stacks 01KP "relative affine-neighborhood characterization"]
theorem Scheme.Hom.isSeparated_iff_exists_affineNeighborhoods_of_sectionPushout
    (f : X ⟶ S) :
    IsSeparated f ↔
      (∀ (x1 x2 : X), f.base x1 = f.base x2 →
        ∃ U V : X.affineOpens,
          x1 ∈ (U : X.Opens) ∧ x2 ∈ (V : X.Opens) ∧
            ∃ W : f.CommonAffineTarget U V,
              IsAffineOpen ((U : X.Opens) ⊓ V) ∧
                Function.Surjective (W.sectionsComparison).hom) := sorry

/-- The relative-pushout affine-neighborhood criterion for separatedness. -/
@[stacks 01KP "relative affine-neighborhood criterion"]
theorem Scheme.Hom.isSeparated_of_exists_affineNeighborhoods_of_sectionPushout
    (f : X ⟶ S)
    (h : ∀ (x1 x2 : X), f.base x1 = f.base x2 →
      ∃ U V : X.affineOpens,
        x1 ∈ (U : X.Opens) ∧ x2 ∈ (V : X.Opens) ∧
          ∃ W : f.CommonAffineTarget U V,
            IsAffineOpen ((U : X.Opens) ⊓ V) ∧
              Function.Surjective (W.sectionsComparison).hom) :
    IsSeparated f := sorry

/-- Lemma 26.21.7 (3): the absolute-tensor affine-neighborhood criterion for separatedness. -/
@[stacks 01KP]
theorem Scheme.Hom.isSeparated_of_exists_affineNeighborhoods
    (f : X ⟶ S)
    (h : ∀ (x1 x2 : X), f.base x1 = f.base x2 →
      ∃ U V : X.affineOpens,
        x1 ∈ (U : X.Opens) ∧ x2 ∈ (V : X.Opens) ∧
          f.HasCommonAffineTarget U V ∧
            IsAffineOpen ((U : X.Opens) ⊓ V) ∧
              Function.Surjective (X.sectionTensorToIntersection U V).hom) :
    IsSeparated f := sorry

end AlgebraicGeometry
