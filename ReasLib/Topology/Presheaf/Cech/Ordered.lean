/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Presheaf.Cech.Coordinates
public import ReasLib.AlgebraicTopology.Cech.OrderedIndex
import Mathlib.Tactic.CrossRefAttribute

/-! @stack 01FI -/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

noncomputable section

universe u v

namespace TopCat.Presheaf.Cech.Ordered

variable {X : TopCat.{u}} {ι : Type v} [LinearOrder ι]

/-- The degree-`p` term of the ordered Cech complex. -/
@[stacks 01FI "ordered Cech term"]
abbrev term (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  AddCommGrpCat.of
    ((σ : OrderedCechIndex ι p) →
      F.obj (op (TopCat.Presheaf.Cech.intersection 𝒰 σ)))

/-- The function underlying the `j`th ordered Cech coface map. -/
def cofaceToFun (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (j : Fin (p + 2)) :
    term 𝒰 F p → term 𝒰 F (p + 1) :=
  fun s σ ↦ TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j))

/-- Additivity of the function underlying an ordered Cech coface map. -/
theorem cofaceToFun_map_add (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (j : Fin (p + 2))
    (s t : term 𝒰 F p) :
    cofaceToFun 𝒰 F p j (s + t) =
      cofaceToFun 𝒰 F p j s + cofaceToFun 𝒰 F p j t := sorry

/-- The `j`th ordered Cech coface map. -/
@[stacks 01FI "ordered Cech coface"]
abbrev coface (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v})
    (p : ℕ) (j : Fin (p + 2)) : term 𝒰 F p ⟶ term 𝒰 F (p + 1) :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (cofaceToFun 𝒰 F p j) (cofaceToFun_map_add 𝒰 F p j)

/-- Evaluating an ordered Cech coface map gives the corresponding restriction map. -/
@[simp]
theorem coface_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) (j : Fin (p + 2))
    (s : term 𝒰 F p) (σ : OrderedCechIndex ι (p + 1)) :
    coface 𝒰 F p j s σ =
      TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j)) := sorry

/-- The alternating ordered Cech differential in degree `p`. -/
@[stacks 01FI "ordered Cech differential"]
abbrev differential (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    term 𝒰 F p ⟶ term 𝒰 F (p + 1) :=
  ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • coface 𝒰 F p j

/-- Evaluating the ordered Cech differential gives its alternating restriction sum. -/
@[simp, stacks 01FI "ordered Cech differential computation"]
theorem differential_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : term 𝒰 F p) (σ : OrderedCechIndex ι (p + 1)) :
    differential 𝒰 F p s σ =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j)) := sorry

/-- Two successive ordered Cech differentials compose to zero. -/
theorem differential_comp (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    differential 𝒰 F p ≫ differential 𝒰 F (p + 1) = 0 := sorry

/-- The ordered Cech complex attached to a family and an ambient linear order. -/
@[stacks 01FI "ordered Cech complex"]
noncomputable def complex (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  CochainComplex.of (term 𝒰 F) (differential 𝒰 F) (differential_comp 𝒰 F)

/-- The degree-`p` object of the ordered Cech complex is its tuplewise term. -/
@[simp, stacks 01FI "ordered Cech degree"]
theorem complex_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (complex 𝒰 F).X p = term 𝒰 F p := sorry

/-- The degree-`p` differential of the ordered Cech complex is the ordered differential. -/
@[simp, stacks 01FI "ordered Cech complex differential"]
theorem complex_d (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (complex 𝒰 F).d p (p + 1) = differential 𝒰 F p := sorry

/-- Coordinate formula for the ordered Cech differential. -/
@[stacks 01FI "ordered Cech differential formula"]
theorem complex_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (complex 𝒰 F).X p) (σ : OrderedCechIndex ι (p + 1)) :
    (complex 𝒰 F).d p (p + 1) s σ =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j)) := sorry

/-- The function induced degreewise by a morphism of coefficient presheaves. -/
def mapToFun (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) (p : ℕ) :
    term 𝒰 F p → term 𝒰 G p :=
  fun s σ ↦ f.app (op (TopCat.Presheaf.Cech.intersection 𝒰 σ)) (s σ)

/-- Additivity of the degreewise map induced by a coefficient morphism. -/
theorem mapToFun_map_add (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) (p : ℕ)
    (s t : term 𝒰 F p) :
    mapToFun 𝒰 f p (s + t) = mapToFun 𝒰 f p s + mapToFun 𝒰 f p t := sorry

/-- The degreewise morphism induced by a morphism of coefficient presheaves. -/
def mapComponent (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) (p : ℕ) :
    term 𝒰 F p ⟶ term 𝒰 G p :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (mapToFun 𝒰 f p) (mapToFun_map_add 𝒰 f p)

/-- Evaluation of the degreewise coefficient map at an ordered tuple. -/
@[simp]
theorem mapComponent_apply (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) (p : ℕ)
    (s : term 𝒰 F p) (σ : OrderedCechIndex ι p) :
    mapComponent 𝒰 f p s σ =
      f.app (op (TopCat.Presheaf.Cech.intersection 𝒰 σ)) (s σ) := sorry

/-- Degreewise coefficient maps commute with the ordered Cech differentials. -/
theorem mapComponent_comm (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    ∀ i j, (ComplexShape.up ℕ).Rel i j →
      mapComponent 𝒰 f i ≫ (complex 𝒰 G).d i j =
        (complex 𝒰 F).d i j ≫ mapComponent 𝒰 f j := sorry

/-- A morphism of coefficient presheaves induces a morphism of ordered Cech complexes. -/
def map (𝒰 : ι → Opens X) {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    complex 𝒰 F ⟶ complex 𝒰 G :=
  HomologicalComplex.Hom.mk (mapComponent 𝒰 f) (mapComponent_comm 𝒰 f)

/-- The degreewise component of the ordered Cech complex map. -/
@[simp]
theorem map_f (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) (p : ℕ) :
    (map 𝒰 f).f p = mapComponent 𝒰 f p := sorry

/-- The ordered Cech complex map of an identity coefficient morphism is the identity. -/
theorem map_id (𝒰 : ι → Opens X) (F : X.Presheaf AddCommGrpCat.{max u v}) :
    map 𝒰 (𝟙 F) = 𝟙 (complex 𝒰 F) := sorry

/-- Ordered Cech complex maps respect composition of coefficient morphisms. -/
theorem map_comp (𝒰 : ι → Opens X)
    {F G H : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) (g : G ⟶ H) :
    map 𝒰 (f ≫ g) = map 𝒰 f ≫ map 𝒰 g := sorry

/-- The ordered Cech complex, functorially in the coefficient presheaf. -/
@[stacks 01FI "ordered Cech complex functor in coefficients"]
noncomputable def complexFunctor (𝒰 : ι → Opens X) :
    X.Presheaf AddCommGrpCat.{max u v} ⥤ CochainComplex AddCommGrpCat.{max u v} ℕ where
  obj F := complex 𝒰 F
  map f := map 𝒰 f
  map_id F := map_id 𝒰 F
  map_comp f g := map_comp 𝒰 f g

/-- The coefficient functor evaluates to the expected ordered Cech complex. -/
@[simp]
theorem complexFunctor_obj (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) :
    (complexFunctor 𝒰).obj F = complex 𝒰 F := sorry

/-- The coefficient functor maps by the canonical ordered Cech complex map. -/
@[simp]
theorem complexFunctor_map (𝒰 : ι → Opens X)
    {F G : X.Presheaf AddCommGrpCat.{max u v}} (f : F ⟶ G) :
    (complexFunctor 𝒰).map f = map 𝒰 f := sorry

section ExplicitOrder

omit [LinearOrder ι]

variable (o : LinearOrder ι)

/-- The ordered Cech complex for an explicitly supplied order.  This is a comparison bridge;
routine APIs should use `complex` with the ambient `[LinearOrder ι]`. -/
@[stacks 01FI "ordered Cech complex with explicit order"]
abbrev complexOfOrder (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) : CochainComplex AddCommGrpCat.{max u v} ℕ :=
  @complex X ι o 𝒰 F

/-- The degree-`p` object of an explicitly ordered complex, with the order argument made visible. -/
theorem complexOfOrder_X (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ) :
    (complexOfOrder o 𝒰 F).X p =
      AddCommGrpCat.of ((σ : @OrderedCechIndex ι o p) →
        F.obj (op (TopCat.Presheaf.Cech.intersection 𝒰 σ))) := sorry

/-- Coordinate formula for the differential of an explicitly ordered complex. -/
theorem complexOfOrder_d_apply (𝒰 : ι → Opens X)
    (F : X.Presheaf AddCommGrpCat.{max u v}) (p : ℕ)
    (s : (complexOfOrder o 𝒰 F).X p) (σ : @OrderedCechIndex ι o (p + 1)) :
    (complexOfOrder o 𝒰 F).d p (p + 1) s σ =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
        TopCat.Presheaf.Cech.restriction 𝒰 F σ j (s (σ.delete j)) := sorry

end ExplicitOrder

end TopCat.Presheaf.Cech.Ordered

end
