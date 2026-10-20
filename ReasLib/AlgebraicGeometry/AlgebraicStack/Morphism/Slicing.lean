module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldFiber
public import Mathlib.RingTheory.Regular.RegularSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Vanishing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation

/-!
# Slicing flat locally finitely presented morphisms to algebraic stacks

A regular sequence on a represented field fibre cuts out a flat, locally
finitely presented morphism after shrinking around the projected fibre point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The structure morphism `V(fs) ∩ W ⟶ X` obtained by composing the inclusion
of the open subspace with `f : U.toGroupoids ⟶ X`. -/
def vanishingToStack {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U)
    (W : AlgebraicSpace.OpenSubspace U) :
    (AlgebraicSpace.vanishingPullback fs W).toGroupoids ⟶ X :=
  AlgebraicSpace.toGroupoids.map
      (AlgebraicSpace.vanishingPullbackι fs W ≫ W.ι) ≫
    f

/-- `vanishingToStack f fs W` is `toGroupoids.map (vanishingPullbackι fs W ≫ W.ι) ≫ f`. -/
theorem vanishingToStack_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} (f : U.toGroupoids ⟶ X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U)
    (W : AlgebraicSpace.OpenSubspace U) :
    vanishingToStack f fs W =
      AlgebraicSpace.toGroupoids.map
          (AlgebraicSpace.vanishingPullbackι fs W ≫ W.ι) ≫
        f :=
  rfl

/-- Let `X` be an algebraic stack over a scheme `S`. Let
`f : U.toGroupoids ⟶ X` be a morphism from an algebraic space which is flat and
locally of finite presentation, and let `p` be a field-valued point of `X`.
Let `fs` be a finite family of global sections of `𝒪_U`, let `F` be an
algebraic-space model of the cartesian field fibre `U ×_X Spec(k)` via an
equivalence `e` with `TwoFibreProduct.apex f p.hom`, and let `z` be a point of
`F` with geometric point `zbar` lying over `z`, such that the images of `fs`
form a regular sequence in `𝒪_{F, zbar}`. Then after replacing `U` by an open
subspace containing the image of `z` in `|U|`, the morphism
`V(fs) ⟶ X` is flat and locally of finite presentation. -/
@[stacks 06MD]
theorem exists_openSubspace_vanishing_flat_locallyOfFinitePresentation
    {S : Scheme.{u}} {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] (f : U.toGroupoids ⟶ X)
    [Flat f] [LocallyOfFinitePresentation f] (p : FieldValuedPoint X) {r : ℕ}
    (fs : Fin r → AlgebraicSpace.globalSectionsRing U) {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (z : AlgebraicSpace.Points F) (zbar : AlgebraicSpace.GeometricPoint F)
    (hz : zbar.liesOver z)
    (hreg : ∀ (V : AlgebraicSpace.smallEtaleSite U)
        (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V),
      RingTheory.Sequence.IsRegular (AlgebraicSpace.etaleLocalRing F zbar)
        (List.ofFn fun i ↦
          globalSectionsToRepresentedFiberEtaleLocalRingAt e zbar V l (fs i))) :
    ∃ W : AlgebraicSpace.OpenSubspace U,
      AlgebraicSpace.Points.map (representedFiberι e) z ∈ W.pointsSet ∧
        Flat (vanishingToStack f fs W) ∧
          LocallyOfFinitePresentation (vanishingToStack f fs W) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
