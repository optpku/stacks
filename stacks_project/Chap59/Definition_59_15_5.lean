module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fpqc.Sheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

/- Definition 59.15.5: a presheaf of sets on schemes over `S` satisfies the
fpqc sheaf property when it is a sheaf for `Scheme.fpqcTopology.over S`. -/
@[stacks 03X6] #check
  (AlgebraicGeometry.isFpqcSheaf :
    (S : Scheme.{u}) →
      (F : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v) →
        Prop)
