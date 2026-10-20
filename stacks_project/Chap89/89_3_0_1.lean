module

public import stacks_project.Chap89.«89_3_0_1_IsoOverClosedPoints»

/-!
# The excision functor at a finite family of closed points
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- 89.3.0.1 The functor `F : C_{X, {x i}} ⥤ ∀ i, C_{U i, u i}` obtained by
base change along affine elementary étale neighbourhoods of a finite family of
pairwise distinct closed points of a decent algebraic space `X`. The neighbourhoods
are shrunk so that the inverse image of `{x i}` in each `U i` is its distinguished
singleton. Each target factor consists of morphisms to `U i` that are isomorphisms
over `U i \ {u i}`. -/
@[stacks 0BHA]
def excisionFamilyFunctor {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U) :
    IsoOverClosedPoints X x hx ⥤
      ∀ i, IsoOverOpen (closedPointComplementι (ofOver ((U i).toOver))
        (isClosed_neighborhoodPoint X x hx U hU i)) :=
  Functor.pi' fun i ↦ ObjectProperty.lift
    (isoOverOpenProperty (closedPointComplementι (ofOver ((U i).toOver))
      (isClosed_neighborhoodPoint X x hx U hU i)))
    (IsoOverOpen.inclusion (closedPointsComplementι X x hx) ⋙
      overPullback (U i).hom)
    (fun Y ↦ (isIsoOverOpen_openInverseImage_iff_closedPointComplement
      X x hx U hU i (isClosed_neighborhoodPoint X x hx U hU i)
      ((overPullback (U i).hom).obj Y.obj).hom).mp
      (IsoOverOpen.baseChange_mem (U i).hom (closedPointsComplementι X x hx) Y))

/-- Each coordinate of `F` has the same underlying base-change object as the
general inverse-image functor `IsoOverClosedPoints.baseChangeFamily`. -/
theorem excisionFamilyFunctor_eq {ι : Type} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) (i : ι) :
    ((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj =
      ((IsoOverClosedPoints.baseChangeFamily X x hx U).obj Y i).obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
