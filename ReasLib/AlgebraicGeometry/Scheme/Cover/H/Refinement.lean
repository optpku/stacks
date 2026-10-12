/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.CategoryTheory.Sites.Family.Covering

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v

namespace AlgebraicGeometry.Scheme.HCovering

/-- An h covering of an affine scheme admits a finite affine refinement arising from a
proper surjective morphism of finite presentation. -/
theorem exists_standardPhRefinement {X : Scheme.{u}} [IsAffine X]
    {ι : Type v} (family : ι → Over X) (hfamily : Scheme.HCovering family) :
    ∃ cover : StandardPhCovering X,
      Scheme.Hom.FinitePresentation cover.toBase ∧
        Refines (ofArrows cover.obj cover.map)
          (ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom)) := sorry

end AlgebraicGeometry.Scheme.HCovering
