module

public import stacks_project.Chap75.Lemma_75_6_2_Coproducts
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits

universe u

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
variable [QuasiCompact f] [QuasiSeparated f]
variable (I : Type u)

/- Lemma 75.6.2: for a scheme `S` and a quasi-separated and quasi-compact morphism
`f : X ⟶ Y` of algebraic spaces over `S`, the restricted derived pushforward
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums. -/
@[stacks 08FB] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward.preservesCoproducts f I :
    PreservesColimitsOfShape (Discrete I) (pushforward f))
