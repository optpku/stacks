module

public import ReasLib.AlgebraicGeometry.QCohStack
import StacksCheckRecall

/-!
# Morphisms in QCohstack

The Hom-sets of the category of pairs `(X, F)` with `X` an `S`-scheme and `F`
quasi-coherent on `X` are the coproducts of pullback Hom-types over morphisms over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- 95.4.0.1 Morphisms (Y, G) ⟶ (X, F) in QCohstack are identified with the coproduct
over f : Y ⟶ X over S of morphisms (QCoh.pullback f.left).obj F ⟶ G in QCoh Y. -/
@[stacks 04U2]
#check (AlgebraicGeometry.QCohStack.homSigma :
  ∀ {S : Scheme.{u}} (x y : AlgebraicGeometry.QCohStack.Obj S),
    (x ⟶ y) ≃
      Σ (f : x.base ⟶ y.base),
        ((AlgebraicGeometry.Scheme.QCoh.pullback f.left).obj y.sheaf ⟶ x.sheaf))
