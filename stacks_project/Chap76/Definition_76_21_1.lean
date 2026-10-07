module

public import stacks_project.Chap76.Definition_76_21_1_NaiveCotangent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/- Definition 76.21.1: Let S be a scheme. Let f : X ⟶ Y be a morphism of algebraic
spaces over S. The naive cotangent complex of f is the complex defined in Modules
on Sites, Definition 18.35.4 for the morphism of ringed topoi f_small between the
small étale sites of X and Y, see Properties of Spaces, Lemma 66.21.3. Notation:
NL_f or NL_{X/Y}. -/
@[stacks 0D0V]
#check (Hom.naiveCotangent f : CochainComplex X.Modules ℤ)

#check (NL[f] : CochainComplex X.Modules ℤ)
