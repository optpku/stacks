/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DoubleZero

/-- The canonical isomorphism exchanging the order in which the zero schemes of two
sections are formed. -/
noncomputable def swapIso {X : Scheme.{u}} (ℒ ℒ' : X.Modules)
    [Modules.Invertible ℒ] [Modules.Invertible ℒ']
    (s : ℒ.sections) (s' : ℒ'.sections) :
    zeroScheme ((Modules.pullback (zeroSchemeι ℒ' s')).obj ℒ)
        (Modules.sectionsPullback (zeroSchemeι ℒ' s') ℒ s) ≅
      zeroScheme ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ')
        (Modules.sectionsPullback (zeroSchemeι ℒ s) ℒ' s') :=
  zeroSchemePullbackIso (zeroSchemeι ℒ' s') ℒ s
      (zeroIdealSheaf_sectionsPullback (zeroSchemeι ℒ' s') ℒ s) ≪≫
    pullbackSymmetry (zeroSchemeι ℒ' s') (zeroSchemeι ℒ s) ≪≫
      (zeroSchemePullbackIso (zeroSchemeι ℒ s) ℒ' s'
        (zeroIdealSheaf_sectionsPullback (zeroSchemeι ℒ s) ℒ' s')).symm

/-- The swapped double zero scheme has the canonical projection to the first zero
scheme. -/
theorem swapIso_hom_fst {X : Scheme.{u}} (ℒ ℒ' : X.Modules)
    [Modules.Invertible ℒ] [Modules.Invertible ℒ']
    (s : ℒ.sections) (s' : ℒ'.sections) :
    (swapIso ℒ ℒ' s s').hom ≫
        zeroSchemeι ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ')
          (Modules.sectionsPullback (zeroSchemeι ℒ s) ℒ' s') =
      zeroSchemePullbackMap (zeroSchemeι ℒ' s') ℒ s
        (zeroIdealSheaf_sectionsPullback (zeroSchemeι ℒ' s') ℒ s) := sorry

/-- The swapped double zero scheme has the canonical projection to the second zero
scheme. -/
theorem swapIso_hom_snd {X : Scheme.{u}} (ℒ ℒ' : X.Modules)
    [Modules.Invertible ℒ] [Modules.Invertible ℒ']
    (s : ℒ.sections) (s' : ℒ'.sections) :
    (swapIso ℒ ℒ' s s').hom ≫
        zeroSchemePullbackMap (zeroSchemeι ℒ s) ℒ' s'
          (zeroIdealSheaf_sectionsPullback (zeroSchemeι ℒ s) ℒ' s') =
      zeroSchemeι ((Modules.pullback (zeroSchemeι ℒ' s')).obj ℒ)
        (Modules.sectionsPullback (zeroSchemeι ℒ' s') ℒ s) := sorry

/-- The canonical swap of double zero schemes respects their structure morphisms to a
common base. -/
theorem swapIso_hom_base {S : Scheme.{u}} {X : Over S}
    (ℒ ℒ' : X.left.Modules) [Modules.Invertible ℒ] [Modules.Invertible ℒ']
    (s : ℒ.sections) (s' : ℒ'.sections) :
    (swapIso ℒ ℒ' s s').hom ≫
        zeroSchemeι ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ')
          (Modules.sectionsPullback (zeroSchemeι ℒ s) ℒ' s') ≫
          zeroSchemeι ℒ s ≫ X.hom =
      zeroSchemeι ((Modules.pullback (zeroSchemeι ℒ' s')).obj ℒ)
          (Modules.sectionsPullback (zeroSchemeι ℒ' s') ℒ s) ≫
        zeroSchemeι ℒ' s' ≫ X.hom := sorry

/-- The canonical interchange of two iterated zero schemes, regarded as schemes over a
common base. -/
noncomputable def swapOverIso {S : Scheme.{u}} {X : Over S}
    (ℒ ℒ' : X.left.Modules) [Modules.Invertible ℒ] [Modules.Invertible ℒ']
    (s : ℒ.sections) (s' : ℒ'.sections) :
    Over.mk
        (zeroSchemeι ((Modules.pullback (zeroSchemeι ℒ' s')).obj ℒ)
            (Modules.sectionsPullback (zeroSchemeι ℒ' s') ℒ s) ≫
          zeroSchemeι ℒ' s' ≫ X.hom) ≅
      Over.mk
        (zeroSchemeι ((Modules.pullback (zeroSchemeι ℒ s)).obj ℒ')
            (Modules.sectionsPullback (zeroSchemeι ℒ s) ℒ' s') ≫
          zeroSchemeι ℒ s ≫ X.hom) :=
  Over.isoMk (swapIso ℒ ℒ' s s') (swapIso_hom_base ℒ ℒ' s s')

/-- The underlying scheme map of the double-zero-scheme interchange is the canonical
swap isomorphism. -/
theorem swapOverIso_hom_left {S : Scheme.{u}} {X : Over S}
    (ℒ ℒ' : X.left.Modules) [Modules.Invertible ℒ] [Modules.Invertible ℒ']
    (s : ℒ.sections) (s' : ℒ'.sections) :
    (swapOverIso ℒ ℒ' s s').hom.left = (swapIso ℒ ℒ' s s').hom := sorry

end AlgebraicGeometry.Scheme.DoubleZero
