module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Module sheaves on slices of the small étale site

Abelian-group-valued sheafification on slice sites supplies the native abelian category
structure on sheaves of modules over the restricted structure sheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Sheafification of abelian-group-valued presheaves on every slice of the small étale site of
an algebraic space is left exact. The adjunction is the actual dense-subsite construction
`smallEtaleTopology_over_hasWeakSheafify`. -/
instance smallEtaleTopology_over_hasSheafify_addCommGrp {S : Scheme.{u}}
    (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    HasSheafify ((smallEtaleTopology X).over U) AddCommGrpCat.{u} where
  isRightAdjoint := inferInstance
  isLeftExact := sorry

end AlgebraicGeometry.AlgebraicSpace
