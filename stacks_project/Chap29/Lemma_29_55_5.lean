module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.RelativeNormalization
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 29.55.5: for a quasi-compact, quasi-separated, dominant morphism of schemes, the
categories of factorizations whose second map is respectively a universal homeomorphism or a
universal homeomorphism inducing residue-field isomorphisms have initial objects. Both initial
factorizations commute with restriction to open subschemes of the target. -/
@[stacks 0H3N] #check
  (AlgebraicGeometry.Scheme.Hom.instHasInitialRelativeWeakNormalizationFactorizations :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f],
      HasInitial (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalizationFactorizations f))

#check
  (AlgebraicGeometry.Scheme.Hom.instHasInitialRelativeSeminormalizationFactorizations :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f],
      HasInitial (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalizationFactorizations f))

#check
  (AlgebraicGeometry.Scheme.Hom.relativeWeakNormalization_openRestrict_exists :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
      (U : X.Opens),
      ∃ (WU : AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalizationFactorizations (f ∣_ U))
          (toGlobal : WU.1.mid ⟶
            (⊥_ (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalizationFactorizations f)).1.mid),
        IsPullback toGlobal WU.1.π
            (⊥_ (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalizationFactorizations f)).1.π
            U.ι ∧
          WU.1.ι ≫ toGlobal =
            (f ⁻¹ᵁ U).ι ≫
              (⊥_ (AlgebraicGeometry.Scheme.Hom.RelativeWeakNormalizationFactorizations f)).1.ι ∧
          Nonempty (IsInitial WU))

#check
  (AlgebraicGeometry.Scheme.Hom.relativeSeminormalization_openRestrict_exists :
    ∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
      (U : X.Opens),
      ∃ (SU : AlgebraicGeometry.Scheme.Hom.RelativeSeminormalizationFactorizations (f ∣_ U))
          (toGlobal : SU.1.mid ⟶
            (⊥_ (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalizationFactorizations f)).1.mid),
        IsPullback toGlobal SU.1.π
            (⊥_ (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalizationFactorizations f)).1.π
            U.ι ∧
          SU.1.ι ≫ toGlobal =
            (f ⁻¹ᵁ U).ι ≫
              (⊥_ (AlgebraicGeometry.Scheme.Hom.RelativeSeminormalizationFactorizations f)).1.ι ∧
          Nonempty (IsInitial SU))
