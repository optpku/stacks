/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Specialization
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry

universe u w

namespace EtaleFundamentalGroup.IsSpecializationMap

/- Lemma 58.16.2 -/
@[stacks 0C0L] #check (EtaleFundamentalGroup.IsSpecializationMap.comp :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f]
    (sbar'' sbar' sbar : Scheme.GeometricPoint S)
    (hSpec₁ : Specializes sbar''.image sbar'.image)
    (hSpec₂ : Specializes sbar'.image sbar.image)
    (F'' : Scheme.FiniteEtale (pullback f sbar''.hom) ⥤ FintypeCat.{w})
    (F' : Scheme.FiniteEtale (pullback f sbar'.hom) ⥤ FintypeCat.{w})
    (F : Scheme.FiniteEtale (pullback f sbar.hom) ⥤ FintypeCat.{w})
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar''.hom))]
    [FiberFunctor F'']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar'.hom))]
    [FiberFunctor F']
    [GaloisCategory (Scheme.FiniteEtale (pullback f sbar.hom))]
    [FiberFunctor F]
    (sp₁ : ContinuousMonoidHom (Aut F'') (Aut F'))
    (hsp₁ : EtaleFundamentalGroup.IsSpecializationMap f sbar'' sbar' hSpec₁ F'' F' sp₁)
    (sp₂ : ContinuousMonoidHom (Aut F') (Aut F))
    (hsp₂ : EtaleFundamentalGroup.IsSpecializationMap f sbar' sbar hSpec₂ F' F sp₂),
    EtaleFundamentalGroup.IsSpecializationMap f sbar'' sbar (hSpec₁.trans hSpec₂) F'' F
      (sp₂.comp sp₁))

end EtaleFundamentalGroup.IsSpecializationMap
