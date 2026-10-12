/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardNeighborhood
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.18.3 (1): an unramified morphism at a point has, over any fixed affine target
neighborhood, an affine source neighborhood immersed into a standard étale presentation by a
monic polynomial localized at its derivative. -/
@[stacks 0CBJ] #check
  (AlgebraicGeometry.Scheme.Hom.UnramifiedAt.exists_affineOpen_immersion_standardEtale :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} (x : X) (V : S.affineOpens),
      f x ∈ (V : S.Opens) → f.UnramifiedAt x →
        ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
          ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
            ∃ P : StandardEtalePair Γ(S, (V : S.Opens)),
              P.g = P.f.derivative ∧
                ∃ j : (U : X.Opens).toScheme ⟶ Spec (CommRingCat.of P.Ring),
                  IsImmersion j ∧
                    j ≫ P.toAffineOpen V = f.resLE (V : S.Opens) (U : X.Opens) e)

/- Lemma 33.18.3 (2): when the morphism is étale at the point, the immersion into the standard
étale presentation can be chosen to be an open immersion. -/
@[stacks 0CBJ] #check
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
