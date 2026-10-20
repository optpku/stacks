/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing.Bounds
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Compactification
namespace Of
namespace UpperShriek

/-- If the target stalk at `f x` is Cohen–Macaulay and the residue-field
transcendence degree at every generic point specializing to `x` is at most `r`,
then a nontrivial degree-`i` cohomology stalk of upper shriek forces
`-(r : ℤ) ≤ i`. -/
theorem neg_trdegBound_le_of_cohomologyStalk_nontrivial
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (x : X.obj.left) (r : ℕ)
    (hCM : Module.CohenMacaulay ((Y.obj.left).presheaf.stalk (f.hom.left x))
      ((Y.obj.left).presheaf.stalk (f.hom.left x)))
    (htrdeg : ∀ ξ : X.obj.left, ξ ∈ genericPoints X.obj.left → Specializes ξ x →
      AlgebraicGeometry.Scheme.Hom.residueFieldTrdegAt f.hom.left ξ ≤ r)
    (i : ℤ)
    (hi : Nontrivial (cohomologyStalk (dualizingObject f P A).obj i x)) :
    -(r : ℤ) ≤ i := sorry

/-- Under the same Cohen–Macaulay and generic-point transcendence-degree
hypotheses, the degree `-r` cohomology stalk of upper shriek satisfies
Serre's condition `(S₂)` over the stalk ring at `x`. -/
theorem cohomologyStalk_serreConditionSTwo
    {S : Scheme.{u}} [IsNoetherian S]
    {X Y : FiniteTypeSeparatedOver S} (f : X ⟶ Y)
    (P : Of Y.obj.left (Over.mk f.hom.left))
    (A : DerivedQCoh.PlusRightAdjoint (ambientMorphism P))
    (x : X.obj.left) (r : ℕ)
    (hCM : Module.CohenMacaulay ((Y.obj.left).presheaf.stalk (f.hom.left x))
      ((Y.obj.left).presheaf.stalk (f.hom.left x)))
    (htrdeg : ∀ ξ : X.obj.left, ξ ∈ genericPoints X.obj.left → Specializes ξ x →
      AlgebraicGeometry.Scheme.Hom.residueFieldTrdegAt f.hom.left ξ ≤ r) :
    Module.SerreConditionS ((X.obj.left).presheaf.stalk x)
      (cohomologyStalk (dualizingObject f P A).obj (-(r : ℤ)) x) 2 := sorry

end UpperShriek
end Of
end Compactification
end Scheme
end AlgebraicGeometry
