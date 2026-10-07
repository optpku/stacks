module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_16_1_Affine
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Rig-flat morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Definition 88.16.1: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism
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
  sorry

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
  sorry

end RigFlat

end AlgebraicGeometry.FormalAlgebraicSpace
