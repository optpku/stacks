/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X X' : Scheme.{u}} (f : X' ⟶ X)
variable (ℒ : X.Modules) [Modules.Invertible ℒ] (s : ℒ.sections)

#check (zeroIdealSheaf_sectionsPullback f ℒ s :
    zeroIdealSheaf ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) =
      (zeroIdealSheaf ℒ s).comap f)

variable (h_zeroIdeal : zeroIdealSheaf ((Modules.pullback f).obj ℒ)
  (Modules.sectionsPullback f ℒ s) = (zeroIdealSheaf ℒ s).comap f)

#check (zeroSchemePullbackIso f ℒ s h_zeroIdeal :
    zeroScheme ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) ≅
      pullback f (zeroSchemeι ℒ s))

#check (zeroSchemePullbackIso_hom_fst f ℒ s h_zeroIdeal :
    (zeroSchemePullbackIso f ℒ s h_zeroIdeal).hom ≫ pullback.fst f (zeroSchemeι ℒ s) =
      zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s))

#check (zeroSchemePullbackMap f ℒ s h_zeroIdeal :
    zeroScheme ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) ⟶
      zeroScheme ℒ s)

#check (zeroSchemePullbackMap_comp f ℒ s h_zeroIdeal :
    zeroSchemePullbackMap f ℒ s h_zeroIdeal ≫ zeroSchemeι ℒ s =
      zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s) ≫ f)

#check (zeroSchemePullback_isPullback f ℒ s h_zeroIdeal :
    IsPullback
      (zeroSchemeι ((Modules.pullback f).obj ℒ) (Modules.sectionsPullback f ℒ s))
      (zeroSchemePullbackMap f ℒ s h_zeroIdeal) f (zeroSchemeι ℒ s))

end AlgebraicGeometry.Scheme
