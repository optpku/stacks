module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.TwoFibreProduct
import StacksCheckRecall

/-!
# Exactness of Inf and T for a 2-fibre product

The canonical six-term sequence for an object of a two-fibre product is exact.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 98.21.6. The canonical six-term sequence of infinitesimal automorphisms
and tangent modules of a two-fibre product is exact. -/
@[stacks 0DNN] #check (AlgebraicGeometry.GroupoidsOver.infTangentSequence_exact :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasStrongRimSchlessinger X] [HasStrongRimSchlessinger Y]
    [HasStrongRimSchlessinger Z] {A : CommRingCat.{u}} {σA : Spec A ⟶ S}
    (w : (apexProjection p q).Fiber (Over.mk σA))
    (M : ModuleCat.{u} A),
    Function.Injective (infProd p q w M) ∧
      Function.Exact (infProd p q w M) (infDiff p q w M) ∧
      Function.Exact (infDiff p q w M) (connecting p q w M) ∧
      Function.Exact (connecting p q w M) (tangentProd p q w M) ∧
      Function.Exact (tangentProd p q w M) (tangentDiff p q w M))
