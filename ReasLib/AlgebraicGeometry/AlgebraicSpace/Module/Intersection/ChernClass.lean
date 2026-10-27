/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Intersection.Number
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.IteratedFirstChern
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Degree

/-!
# Chern-class formulas for intersection numbers on algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Modules.Intersection

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The intersection number of `d` invertible modules with a dimension-`d`
closed subspace of a proper algebraic space over a field is the Chow degree of
their iterated first-Chern cap product with the associated cycle of the subspace. -/
theorem number_eq_chowDegree_iteratedFirstChernClassCap
    {k : Type u} [Field k]
    {X Z : AlgebraicSpace (Spec (CommRingCat.of k))}
    (i : Z ⟶ X) [IsClosedImmersion i] [Proper (SchemeRealization.toBase X)]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    {d : ℕ} (hZdim : dimension Z = d)
    [Abelian X.Modules] [Abelian Z.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions Z.Modules]
    (L : Fin d → X.Modules) [∀ j : Fin d, isInvertibleObject (L j)] :
    number i hZdim L =
      (chowDegree
        (iteratedFirstChernClassCap (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) d L
          (closedSubspaceClass (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ))
            (ClosedSubspace.ofι i) d)) : ℚ) :=
  sorry

end Modules.Intersection
end AlgebraicGeometry.AlgebraicSpace
