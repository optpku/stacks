module

public import stacks_project.Chap86.Lemma_86_8_1_Coproduct
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

/- Lemma 86.8.1: if `Y` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` and `f : X ⟶ Y` is proper, flat, and of finite presentation, then any right
adjoint `a` of `Rf_*` on `DerivedQCoh` (Lemma 86.3.1) commutes with arbitrary direct
sums. -/
@[stacks 0E5T] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_preservesCoproducts_of_proper_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X), (pushforwardCohomologyIn f ⊣ a) →
      (I : Type u) → PreservesColimitsOfShape (Discrete I) a)
