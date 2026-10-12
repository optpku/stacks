/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.SmallCarrierUniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.SmallInjectiveResolution

/-!
# Higher direct images of associated modules on small sites

This module compares small-site higher direct images of associated modules with
the associated modules of scheme-theoretic higher direct images.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- For a quasi-compact and quasi-separated scheme morphism, higher direct image
on the small Zariski site preserves the associated-module comparison. -/
theorem higherDirectImage_isomorphic_smallZariski
    {T S : Scheme.{u}} (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : T.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic
      (AlgebraicGeometry.Scheme.Zariski.Small.higherDirectImageModule f
        (smallCarrierUniverseLift .zariski T F) i)
      (smallCarrierUniverseLift .zariski S
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F i)) := sorry

/-- For a quasi-compact and quasi-separated scheme morphism, higher direct image
on the small étale site preserves the associated-module comparison. -/
theorem higherDirectImage_isomorphic_smallEtale
    {T S : Scheme.{u}} (f : T ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (F : T.Modules) [F.IsQuasicoherent] (i : ℕ) :
    IsIsomorphic
      (AlgebraicGeometry.Scheme.Etale.Small.higherDirectImageModule f
        (smallCarrierUniverseLift .etale T F) i)
      (smallCarrierUniverseLift .etale S
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F i)) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
