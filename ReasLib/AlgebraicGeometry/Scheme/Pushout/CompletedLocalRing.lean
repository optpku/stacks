module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.AlgebraicGeometry.Scheme.LocalRing.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.SurjectivePullback
public import ReasLib.RingTheory.AdicCompletion.LocalMap

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Pushout

/-- In the pushout of a separated finite-type scheme `X'` of dimension at most one
with `Spec k'` along `Spec (∀ j, k'₁ j)`, the completed local ring at the image point
and the product of the completed local rings at the branch points form a pullback
square over `k'` and the product of the branch fields. The maps from the completed
local rings to these fields are the canonical residue-field maps. -/
theorem completedLocalRingSquareIsPullback
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    {ι : Type u} [Fintype ι] [Nonempty ι]
    (k'₁ : ι → Type u) [∀ j, Field (k'₁ j)] [∀ j, Algebra k' (k'₁ j)]
    [∀ j, FiniteDimensional k' (k'₁ j)] [∀ j, Algebra k (k'₁ j)]
    [∀ j, IsScalarTower k k' (k'₁ j)]
    (X X' : SchemeOverField k) [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
    (h_dimension : topologicalKrullDim X'.left ≤ 1)
    (i' : (Over.mk (Spec.map (CommRingCat.ofHom
      (algebraMap k ((j : ι) → k'₁ j)))) : SchemeOverField k) ⟶ X')
    [IsClosedImmersion i'.left]
    (a : X' ⟶ X)
    (i : (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :
      SchemeOverField k) ⟶ X)
    [Surjective (Spec.map (CommRingCat.ofHom (algebraMap k' ((j : ι) → k'₁ j))))]
    (h_pushout : IsPushout i'.left
      (Spec.map (CommRingCat.ofHom (algebraMap k' ((j : ι) → k'₁ j)))) a.left i.left)
    (x : X.left) (x' : ι → X'.left)
    (h_x : i.left (IsLocalRing.closedPoint k') = x)
    (h_x' : ∀ j,
      (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ k'₁ j) j)) ≫ i'.left)
          (IsLocalRing.closedPoint (k'₁ j)) = x' j)
    (h_image : ∀ j, a.left (x' j) = x) :
    IsPullback
      (CommRingCat.ofHom (((Scheme.SpecToEquivOfField k' X.left i.left).2.hom.comp
        (X.left.residueFieldCongr h_x.symm).hom.hom).comp
          (Scheme.completedStalkResidueFieldMap X.left x)))
      (CommRingCat.ofHom (RingHom.pi fun j ↦
        h_image j ▸ AdicCompletion.mapLocal (a.left.stalkMap (x' j)).hom))
      (CommRingCat.ofHom (RingHom.pi fun j ↦ algebraMap k' (k'₁ j)))
      (CommRingCat.ofHom (RingHom.pi fun j ↦
        (((Scheme.SpecToEquivOfField (k'₁ j) X'.left
          (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j ↦ k'₁ j) j)) ≫
            i'.left)).2.hom.comp
              (X'.left.residueFieldCongr (h_x' j).symm).hom.hom).comp
            (Scheme.completedStalkResidueFieldMap X'.left (x' j))).comp
              (Pi.evalRingHom (fun j ↦ AdicCompletion
                (IsLocalRing.maximalIdeal ((X'.left.presheaf).stalk (x' j)))
                ((X'.left.presheaf).stalk (x' j))) j))) := sorry

end AlgebraicGeometry.Scheme.Pushout
