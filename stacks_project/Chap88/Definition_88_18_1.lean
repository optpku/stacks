/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1_Affine
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Rig-smooth morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Definition 88.18.1: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism
of locally Noetherian formal algebraic spaces over `S`. The morphism `f` is
rig-smooth if every commutative square with affine formal algebraic spaces `U`,
`V` and étale maps `U ⟶ X`, `V ⟶ Y` representable by algebraic spaces has
`U ⟶ V` corresponding to a rig-smooth map of adic Noetherian topological
rings. -/
@[stacks 0GCP]
class RigSmooth {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) : Prop where
  /-- Affine étale charts detect rig-smoothness of `f` by a rig-smooth map of
  adic Noetherian topological rings. -/
  of_affineEtaleChart :
    ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace U] [IsAffine U]
      [IsFormalAlgebraicSpace V] [IsAffine V]
      {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
      CommSq g u v f → Etale u → Etale v → AffineFormalAlgebraicSpace.RigSmooth g

namespace RigSmooth

/-- The identity of a locally Noetherian formal algebraic space is rig-smooth. -/
instance id {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] : RigSmooth (𝟙 X) :=
  sorry

/-- Affine étale chart squares over a rig-smooth morphism have rig-smooth
horizontal arrows. -/
theorem of_commSq {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigSmooth f] {U V : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace U] [IsAffine U]
    [IsFormalAlgebraicSpace V] [IsAffine V]
    {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V}
    (h : CommSq g u v f) [Etale u] [Etale v] :
    AffineFormalAlgebraicSpace.RigSmooth g :=
  sorry

/-- A morphism of locally Noetherian formal algebraic spaces is rig-smooth if and
only if every affine étale chart square has a rig-smooth horizontal arrow of
affine formal algebraic spaces. -/
theorem iff {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y) :
    RigSmooth f ↔
      ∀ {U V : (Over S)ᵒᵖ ⥤ Type u}
        [IsFormalAlgebraicSpace U] [IsAffine U]
        [IsFormalAlgebraicSpace V] [IsAffine V]
        {u : U ⟶ X} {v : V ⟶ Y} {g : U ⟶ V},
        CommSq g u v f → Etale u → Etale v →
          AffineFormalAlgebraicSpace.RigSmooth g :=
  sorry

end RigSmooth

end AlgebraicGeometry.FormalAlgebraicSpace
