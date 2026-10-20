module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.LocallyRinged
public import stacks_project.Chap66.Lemma_66_18_8_Topos
public import stacks_project.Chap66.Lemma_66_29_7_CommSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.commStructureSheafLift_isLocallyRinged :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (AlgebraicGeometry.AlgebraicSpace.commStructureSheafLift X).IsLocallyRinged)

end AlgebraicGeometry.AlgebraicSpace
