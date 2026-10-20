/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization.SmoothProper
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

/- Proposition 58.30.2: if `f : X ⟶ S` is smooth and proper with geometrically
connected fibres, and `s' ↝ s` is a specialization with `ringChar κ(s) = 0`,
then the étale specialization map `π₁(X_{s̄'}) → π₁(X_{s̄})` is an isomorphism. -/
@[stacks 0C0Q] #check (EtaleFundamentalGroup.IsSpecializationMap.bijective :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    (hchar : ringChar (S.residueField sbar.image) = 0)
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec F' F sp),
    Function.Bijective sp)
