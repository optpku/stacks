/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Gluing.OpenFamily.Uniqueness
import Mathlib.Tactic.CrossRefAttribute

/-!
# Overlap isomorphisms for open-family gluing

This file provides restriction, compatibility, uniqueness, and cocycle API for isomorphisms on
pairwise overlaps.  The comparison between iterated and direct restriction remains explicit.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily

open OpenSubspace.Restriction

variable {X : RingedSpace.{u}} {𝓑 : Set (Opens X.carrier)}

/-- Restrict an overlap isomorphism to a smaller open, transporting both iterated restrictions to
the corresponding direct restrictions. -/
@[stacks 0D69 "restriction of a derived overlap isomorphism"]
noncomputable def restrictOverlapIso {U V W : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    (e : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B)
    (hW : W ≤ U ⊓ V) :
    (derivedBetween X (hW.trans inf_le_left)).obj A ≅
      (derivedBetween X (hW.trans inf_le_right)).obj B :=
  ((derivedBetweenCompIso X hW inf_le_left).app A).symm ≪≫
    (derivedBetween X hW).mapIso e ≪≫
      (derivedBetweenCompIso X hW inf_le_right).app B

/-- An overlap isomorphism is compatible with the gluing datum when all its restrictions to
smaller family members identify the prescribed transition maps. -/
@[stacks 0D69 "compatibility of a derived overlap isomorphism"]
def IsOverlapCompatible (G : Gluing.OpenFamily X 𝓑)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑)
    (e : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
      (derivedBetween X inf_le_right).obj (G.obj V hV)) : Prop :=
  ∀ ⦃W : Opens X.carrier⦄ (hW : W ∈ 𝓑) (hWUV : W ≤ U ⊓ V),
    CommSq (restrictOverlapIso e hWUV).hom
      (G.ρ U W hU hW (hWUV.trans inf_le_left)).hom
      (G.ρ V W hV hW (hWUV.trans inf_le_right)).hom (𝟙 (G.obj W hW))

/-- Compatible overlap isomorphisms exist uniquely under overlap generation and local negative
self-Ext vanishing. -/
@[stacks 0D69 "unique compatible derived overlap isomorphism"]
theorem existsUniqueOverlapIso (G : Gluing.OpenFamily X 𝓑)
    (hoverlap : GeneratesOverlaps X 𝓑) (hneg : G.NegativeSelfExtVanishing)
    {U V : Opens X.carrier} (hU : U ∈ 𝓑) (hV : V ∈ 𝓑) :
    ∃! e : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
        (derivedBetween X inf_le_right).obj (G.obj V hV),
      G.IsOverlapCompatible hU hV e := sorry

/-- One restriction square of a compatible overlap isomorphism. -/
@[stacks 0D69 "restriction square of a compatible overlap isomorphism"]
theorem IsOverlapCompatible.commSq {G : Gluing.OpenFamily X 𝓑}
    {U V W : Opens X.carrier} {hU : U ∈ 𝓑} {hV : V ∈ 𝓑}
    {e : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
      (derivedBetween X inf_le_right).obj (G.obj V hV)}
    (he : G.IsOverlapCompatible hU hV e) (hW : W ∈ 𝓑) (hWUV : W ≤ U ⊓ V) :
    CommSq (restrictOverlapIso e hWUV).hom
      (G.ρ U W hU hW (hWUV.trans inf_le_left)).hom
      (G.ρ V W hV hW (hWUV.trans inf_le_right)).hom (𝟙 (G.obj W hW)) := sorry

/-- Equational form of a compatible overlap restriction square. -/
@[stacks 0D69 "restriction equation for a compatible overlap isomorphism"]
theorem IsOverlapCompatible.w {G : Gluing.OpenFamily X 𝓑}
    {U V W : Opens X.carrier} {hU : U ∈ 𝓑} {hV : V ∈ 𝓑}
    {e : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
      (derivedBetween X inf_le_right).obj (G.obj V hV)}
    (he : G.IsOverlapCompatible hU hV e) (hW : W ∈ 𝓑) (hWUV : W ≤ U ⊓ V) :
    (restrictOverlapIso e hWUV).hom ≫
        (G.ρ V W hV hW (hWUV.trans inf_le_right)).hom =
      (G.ρ U W hU hW (hWUV.trans inf_le_left)).hom := sorry

/-- Compatible overlap isomorphisms are equal. -/
@[stacks 0D69 "uniqueness of compatible derived overlap isomorphisms"]
theorem eq_of_isOverlapCompatible (G : Gluing.OpenFamily X 𝓑)
    (hoverlap : GeneratesOverlaps X 𝓑) (hneg : G.NegativeSelfExtVanishing)
    {U V : Opens X.carrier} {hU : U ∈ 𝓑} {hV : V ∈ 𝓑}
    {e e' : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
      (derivedBetween X inf_le_right).obj (G.obj V hV)}
    (he : G.IsOverlapCompatible hU hV e) (he' : G.IsOverlapCompatible hU hV e') :
    e = e' := sorry

/-- Remark 20.45.5: compatible overlap isomorphisms satisfy the cocycle condition on triple
intersections. -/
@[stacks 0D69 "cocycle condition for compatible derived overlap isomorphisms"]
theorem overlapCocycle (G : Gluing.OpenFamily X 𝓑)
    (hoverlap : GeneratesOverlaps X 𝓑) (hneg : G.NegativeSelfExtVanishing)
    {U V W : Opens X.carrier} {hU : U ∈ 𝓑} {hV : V ∈ 𝓑} {hW : W ∈ 𝓑}
    {eUW : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
      (derivedBetween X inf_le_right).obj (G.obj W hW)}
    {eUV : (derivedBetween X inf_le_left).obj (G.obj U hU) ≅
      (derivedBetween X inf_le_right).obj (G.obj V hV)}
    {eVW : (derivedBetween X inf_le_left).obj (G.obj V hV) ≅
      (derivedBetween X inf_le_right).obj (G.obj W hW)}
    (heUW : G.IsOverlapCompatible hU hW eUW)
    (heUV : G.IsOverlapCompatible hU hV eUV)
    (heVW : G.IsOverlapCompatible hV hW eVW) :
    restrictOverlapIso eUW (le_inf (inf_le_left.trans inf_le_left) inf_le_right) =
      restrictOverlapIso eUV inf_le_left ≪≫
        restrictOverlapIso eVW
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.OpenFamily

end
