/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization.DiscreteValuation
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

/- Lemma 58.16.4: every specialization map for a proper morphism with geometrically
connected fibres over a Noetherian scheme is induced, up to geometric field-extension
comparisons, by a strictly henselian discrete valuation ring over the base. -/
@[stacks 0C0N] #check
  (EtaleFundamentalGroup.IsSpecializationMap.exists_strictHenselianDvr :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp)
    [IsNoetherian S],
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R)
      (_ : IsDiscreteValuationRing R) (_ : StrictHenselianLocalRing R)
      (k : Spec (CommRingCat.of R) ⟶ S),
      EtaleFundamentalGroup.IsSpecializationMap.dvrInduced f sbar' sbar F' F sp R k)
