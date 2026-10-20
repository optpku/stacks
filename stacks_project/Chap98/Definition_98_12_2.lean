/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver

universe u

/- Definition 98.12.2
Let S be a locally Noetherian scheme. Let 𝒳 be fibred in groupoids over
(Sch/S)_fppf. Let U be a scheme locally of finite type over S. Let x be an
object of 𝒳 lying over U. Let u0 be a finite type point of U. We say x is
versal at u0 if the morphism hat x of predeformation categories from
98.12.1.1 is smooth in the sense of BasedFunctor.IsSmooth
(Definition 90.8.1). -/
@[stacks 07XF] #check (AlgebraicGeometry.GroupoidsOver.IsVersalAt.iff :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0],
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (residueFieldType u0)] [Module.Finite Λ (residueFieldType u0)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ (residueFieldType u0))) ≫
              openImmersion =
            fromResidueField u0 ≫ hU),
        BasedFunctor.IsSmooth (hat hU x hx u0 openImmersion h_factor))
