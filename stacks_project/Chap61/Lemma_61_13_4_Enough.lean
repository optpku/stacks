module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.EnoughObjects
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Lemma_61_12_20_Affine
public import stacks_project.Chap61.Lemma_61_12_21_AffineIndEtale
public import stacks_project.Chap61.Definition_61_12_8_Affine

/-!
# Enough weakly contractible objects on pro-étale sites

The small, big-slice, affine, big-affine, and affine ind-étale pro-étale
topologies of a scheme have enough weakly contractible objects in the sense
of `HasEnoughObjectsWithProperty`. On the non-affine sites the covering
objects may be taken affine (hence quasi-compact).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.ProEt

/-- The small pro-étale topology of a scheme has enough affine weakly
contractible objects. Affine schemes are quasi-compact. -/
theorem hasEnough_isAffine_isWeaklyContractible (S : Scheme.{u}) :
    (topology S).HasEnoughObjectsWithProperty
      (fun U ↦ IsAffine U.left ∧ (topology S).IsWeaklyContractible U) := sorry

/-- The small pro-étale topology of a scheme has enough weakly contractible
objects. -/
theorem hasEnough_isWeaklyContractible (S : Scheme.{u}) :
    (topology S).HasEnoughObjectsWithProperty (topology S).IsWeaklyContractible :=
  sorry

/-- The affine small pro-étale topology of a scheme has enough weakly
contractible objects. -/
theorem hasEnough_isWeaklyContractible_affine (S : Scheme.{u}) :
    (affineTopology S).HasEnoughObjectsWithProperty
      (affineTopology S).IsWeaklyContractible := sorry

/-- The affine ind-étale small pro-étale topology of an affine scheme has enough
weakly contractible objects. -/
theorem hasEnough_isWeaklyContractible_affineIndEtale (S : Scheme.{u}) [IsAffine S] :
    (affineIndEtaleTopology S).HasEnoughObjectsWithProperty
      (affineIndEtaleTopology S).IsWeaklyContractible := sorry

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.Scheme

/-- The big pro-étale topology of schemes over `S` has enough affine weakly
contractible objects. Affine schemes are quasi-compact. -/
theorem hasEnough_isAffine_isWeaklyContractible_proetaleOver (S : Scheme.{u}) :
    (proetaleTopology.over S).HasEnoughObjectsWithProperty
      (fun U ↦ IsAffine U.left ∧
        (proetaleTopology.over S).IsWeaklyContractible U) := sorry

/-- The big pro-étale topology of schemes over `S` has enough weakly
contractible objects. -/
theorem hasEnough_isWeaklyContractible_proetaleOver (S : Scheme.{u}) :
    (proetaleTopology.over S).HasEnoughObjectsWithProperty
      (proetaleTopology.over S).IsWeaklyContractible := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen big affine pro-étale topology of a scheme has enough weakly
contractible objects. -/
theorem hasEnough_isWeaklyContractible_bigAffine
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    (bigAffineTopology X S).HasEnoughObjectsWithProperty
      (bigAffineTopology X S).IsWeaklyContractible := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
