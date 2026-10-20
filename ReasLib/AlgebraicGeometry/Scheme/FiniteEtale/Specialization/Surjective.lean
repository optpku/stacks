/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

namespace EtaleFundamentalGroup.IsSpecializationMap

/-- For a flat proper morphism with geometrically connected fibers, a specialization map
to a geometrically reduced special fiber is surjective. -/
theorem surjective {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [GeometricallyConnected f]
    (sbar' sbar : Scheme.GeometricPoint S)
    (hSpec : Specializes sbar'.image sbar.image)
    [GeometricallyReduced (f.fiberToSpecResidueField sbar.image)]
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp : EtaleFundamentalGroup.IsSpecializationMap
      f sbar' sbar hSpec F' F sp) :
    Function.Surjective sp := sorry

end EtaleFundamentalGroup.IsSpecializationMap
