/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import ReasLib.AlgebraicGeometry.Scheme.Limit.DirectedAffine

/-!
# Closed subschemes in limits of cofinal open neighborhoods

A closed subset of a scheme, equipped with its reduced induced structure,
maps compatibly to every open neighborhood in a cofinal inverse system. This
module constructs the resulting morphism to a limit and records its closed
immersion property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood

/-- The reduced closed subscheme on `T` maps compatibly to every member of a
directed inverse system of open neighborhoods of `T`. -/
noncomputable def closedSubschemeCone
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
    (D : OrderDual I ⥤ Scheme.{u})
    (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
    [openImmersion : ∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
    (hT_mem : ∀ i : OrderDual I, T ⊆
      (SetLike.coe (ι.app i).opensRange : Set S)) :
    Cone D :=
  let Z := Scheme.ClosedSubschemeStructure.reduced ⟨T, hT⟩
  let j : Z.subscheme ⟶ S := Z.ι
  have hj : Set.range j = (⟨T, hT⟩ : TopologicalSpace.Closeds S) := by
    simpa only [j] using Z.range_ι
  { pt := Z.subscheme
    π :=
      { app := fun i ↦
          let k : D.obj i ⟶ S := ι.app i
          (@IsOpenImmersion.lift _ _ _ k j
            (show IsOpenImmersion k from openImmersion i) (by
            rw [hj]
            intro y hy
            exact (@Scheme.Hom.mem_opensRange _ _ (ι.app i) (openImmersion i) y).mp
              (hT_mem i hy)) :
            Z.subscheme ⟶ D.obj i)
        naturality := sorry } }

/-- The canonical morphism from the reduced closed subscheme on `T` to a
limit of a directed inverse system of open neighborhoods of `T`. -/
noncomputable def closedSubschemeLift
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
    (D : OrderDual I ⥤ Scheme.{u})
    (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c)
    [openImmersion : ∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
    (hT_mem : ∀ i : OrderDual I, T ⊆
      (SetLike.coe (ι.app i).opensRange : Set S)) :
    (Scheme.ClosedSubschemeStructure.reduced ⟨T, hT⟩).subscheme ⟶ c.pt :=
  hc.lift (closedSubschemeCone hT D ι hT_mem)

/-- Composing the canonical limit lift with the compatible morphism to `S`
recovers the reduced closed-subscheme inclusion. -/
theorem closedSubschemeLift_comp
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
    (D : OrderDual I ⥤ Scheme.{u})
    (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S)
    (hπ : ∀ i : OrderDual I, c.π.app i ≫ ι.app i = s)
    [openImmersion : ∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
    (hT_mem : ∀ i : OrderDual I, T ⊆
      (SetLike.coe (ι.app i).opensRange : Set S)) :
    closedSubschemeLift hT D ι c hc hT_mem ≫ s =
      (Scheme.ClosedSubschemeStructure.reduced ⟨T, hT⟩).ι := sorry

/-- For a cofinal directed inverse system of open neighborhoods with affine
transition morphisms, the canonical morphism from the reduced closed
subscheme on `T` to the limit is a closed immersion. -/
theorem closedSubschemeLift_isClosedImmersion
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {T : Set S} (hT : IsClosed T)
    (D : OrderDual I ⥤ Scheme.{u})
    (ι : D ⟶ (Functor.const (OrderDual I)).obj S)
    (c : Cone D) (hc : IsLimit c) (s : c.pt ⟶ S)
    (hπ : ∀ i : OrderDual I, c.π.app i ≫ ι.app i = s)
    [openImmersion : ∀ i : OrderDual I, IsOpenImmersion (ι.app i)]
    (hT_mem : ∀ i : OrderDual I, T ⊆
      (SetLike.coe (ι.app i).opensRange : Set S))
    (hι_cofinal : ∀ W : S.Opens, T ⊆ (W : Set S) →
      ∃ i : OrderDual I, (ι.app i).opensRange ≤ W)
    [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))] :
    IsClosedImmersion (closedSubschemeLift hT D ι c hc hT_mem) := sorry

end AlgebraicGeometry.Scheme.Limit.CofinalOpenNeighborhood
