module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardNeighborhood
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Theorem 41.12.3: an étale morphism at a point has, over any fixed affine target
neighborhood, an affine source neighborhood openly immersed into a standard étale presentation
by a monic polynomial localized at its derivative. -/
@[stacks 025C] #check
  (AlgebraicGeometry.Scheme.Hom.EtaleAt.exists_affineOpen_openImmersion_standardEtale :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} (x : X) (V : S.affineOpens),
      f x ∈ (V : S.Opens) → f.EtaleAt x →
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
            ∃ P : StandardEtalePair Γ(S, (V : S.Opens)),
              P.g = P.f.derivative ∧
                ∃ j : (U : X.Opens).toScheme ⟶ Spec (CommRingCat.of P.Ring),
                  IsOpenImmersion j ∧
                    j ≫ P.toAffineOpen V = f.resLE (V : S.Opens) (U : X.Opens) e)
