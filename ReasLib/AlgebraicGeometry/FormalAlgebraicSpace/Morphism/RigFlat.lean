/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineRigFlat
public import Mathlib.CategoryTheory.CommSq
import Mathlib.Tactic.CrossRefAttribute

/-!
# Rig-flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Let `S` be a scheme, and let `f : X ⟶ Y` be a morphism
of locally Noetherian formal algebraic spaces over `S`. The morphism `f` is
rig-flat if every commutative square with affine formal algebraic spaces `U`,
`V` and étale maps `U ⟶ X`, `V ⟶ Y` representable by algebraic spaces has
`U ⟶ V` corresponding to a rig-flat map of adic Noetherian topological
rings. -/
@[stacks 0GGX]
class RigFlat {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) : Prop where
  /-- Affine étale charts detect rig-flatness of `f` by a rig-flat map of
  adic Noetherian topological rings. -/
  of_affineEtaleChart :
    ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace U] [IsAffine U]
      [IsFormalAlgebraicSpace V] [IsAffine V]
      {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
      CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigFlat g

namespace RigFlat

/-- The identity of a locally Noetherian formal algebraic space is rig-flat. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] : RigFlat (𝟙 X) :=
  sorry

/-- Affine étale chart squares over a rig-flat morphism have rig-flat
horizontal arrows. -/
theorem of_commSq {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigFlat f] {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V}
    (h : CommSq g u v f) [Etale u] [Etale v] :
    AffineFormalAlgebraicSpace.RigFlat g :=
  RigFlat.of_affineEtaleChart (f := f) h inferInstance inferInstance

/-- A morphism of locally Noetherian formal algebraic spaces is rig-flat if and
only if every affine étale chart square has a rig-flat horizontal arrow of
affine formal algebraic spaces. -/
theorem iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) :
    RigFlat f ↔
      ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
        [IsFormalAlgebraicSpace U] [IsAffine U]
        [IsFormalAlgebraicSpace V] [IsAffine V]
        {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
        CommSq g u v f → Etale u → Etale v →
          AffineFormalAlgebraicSpace.RigFlat g :=
  ⟨fun h => h.of_affineEtaleChart, fun h => ⟨h⟩⟩

end RigFlat

end AlgebraicGeometry.FormalAlgebraicSpace
