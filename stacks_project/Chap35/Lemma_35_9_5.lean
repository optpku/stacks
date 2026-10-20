module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.HigherDirectImage
import StacksCheckRecall

/-!
# Higher direct images on small standard sites

This source bridge records the small-Zariski and small-étale higher-direct-image
comparisons for associated quasi-coherent modules.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 35.9.5 (1): on the small Zariski site, higher direct image of the associated
module is isomorphic to the module associated to the usual higher direct image. -/
@[stacks 071N]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.higherDirectImage_isomorphic_smallZariski :
    ∀ {T S : Scheme.{u}} (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (F : T.Modules) [F.IsQuasicoherent] (i : ℕ),
      IsIsomorphic
        (Scheme.Zariski.Small.higherDirectImageModule f
          (Scheme.AssociatedModule.smallCarrierUniverseLift .zariski T F) i)
        (Scheme.AssociatedModule.smallCarrierUniverseLift .zariski S
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F i)))

/- Lemma 35.9.5 (2): on the small étale site, higher direct image of the associated
module is isomorphic to the module associated to the usual higher direct image. -/
@[stacks 071N]
#check
  (AlgebraicGeometry.Scheme.AssociatedModule.higherDirectImage_isomorphic_smallEtale :
    ∀ {T S : Scheme.{u}} (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
      (F : T.Modules) [F.IsQuasicoherent] (i : ℕ),
      IsIsomorphic
        (Scheme.Etale.Small.higherDirectImageModule f
          (Scheme.AssociatedModule.smallCarrierUniverseLift .etale T F) i)
        (Scheme.AssociatedModule.smallCarrierUniverseLift .etale S
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F i)))
