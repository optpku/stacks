module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Over.StalkGluing
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Lemma 32.6.4: restriction to the complement of a closed point and to its local scheme is
bijective onto compatible pairs of morphisms over the base. -/
@[stacks 0GWT] #check
  (AlgebraicGeometry.morphismsOverRestrictPuncturedLocalSpecBijective :
    ∀ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S),
      [LocallyOfFinitePresentation pY] →
      ∀ (x : X), x ∈ closedPoints X →
        ∀ (U : X.Opens), (U : Set X) = ({x} : Set X)ᶜ →
          [QuasiCompact U.ι] →
          Set.BijOn
            (fun g : {g : X ⟶ Y // g ≫ pY = pX} ↦
              (U.ι ≫ g.1, X.fromSpecStalk x ≫ g.1))
            Set.univ
            ({ab : (U.toScheme ⟶ Y) ×
                ((Spec (CommRingCat.of (X.presheaf.stalk x))) ⟶ Y) |
                ab.1 ≫ pY = U.ι ≫ pX} ∩
              {ab | ab.2 ≫ pY = X.fromSpecStalk x ≫ pX} ∩
              {ab | (X.fromSpecStalk x ∣_ U) ≫ ab.1 =
                (stalkOpenIntersection X U x).ι ≫ ab.2}))

end AlgebraicGeometry
