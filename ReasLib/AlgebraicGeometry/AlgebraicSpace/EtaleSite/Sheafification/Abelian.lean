module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SmallAtlas

/-!
# Abelian sheafification through the actual small atlas

The small affine étale atlas site uses the atlas carried by the algebraic
space. Its native sheafification and right Kan extension supply sheafification
on the presentation site in the original coefficient universe.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Sheafification of abelian presheaves uses the actual small affine atlas. -/
theorem smallEtaleAbelianSheafification {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u} := by
  let U := AtlasInput.scheme X
  let a := AtlasInput.map X
  letI : AlgebraicSpace.Etale a := AtlasInput.etale X
  letI : (PullbackFactory.SmallAtlas.inclusion U a).IsDenseSubsite
      (PullbackFactory.SmallAtlas.topology U a) (smallEtaleTopology X) :=
    PullbackFactory.SmallAtlas.denseSubsite U a (AtlasInput.locallySurjective X)
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence
    (PullbackFactory.SmallAtlas.topology U a) (smallEtaleTopology X)
    (PullbackFactory.SmallAtlas.inclusion U a) AddCommGrpCat.{u}

end AlgebraicGeometry.AlgebraicSpace
