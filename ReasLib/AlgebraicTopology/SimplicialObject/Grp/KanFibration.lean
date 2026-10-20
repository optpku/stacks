/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Underlying.KanFibration
public import ReasLib.AlgebraicTopology.SimplicialObject.Underlying.Surjective
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
@stack 08NZ

# Kan fibrations from simplicial groups

Underlying simplicial sets of simplicial groups are Kan complexes, and epimorphisms of simplicial
groups induce Kan fibrations. Concrete surjectivity statements are exported as companion bridges.
-/

@[expose] public section

open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace CategoryTheory.SimplicialObject.Grp

namespace underlying

/-- 08NZ (Lemma 14.31.6): the underlying simplicial set of a simplicial group is a Kan complex. -/
@[stacks 08NZ "simplicial groups are Kan complexes"]
instance kanComplex (X : SimplicialObject GrpCat.{u}) :
    SSet.KanComplex (X ⋙ forget GrpCat) := sorry

/-- Degreewise surjectivity characterizes epimorphisms of simplicial groups. -/
@[stacks 08P0 "degreewise-surjective epimorphisms of simplicial groups"]
theorem epi_iff_surjective {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n) := sorry

/-- Epimorphisms of simplicial groups lie in the morphism property detected by underlying Kan
fibrations. -/
@[stacks 08P0 "epimorphisms of simplicial groups induce Kan fibrations"]
theorem epimorphisms_le_fibrations :
    MorphismProperty.epimorphisms (SimplicialObject GrpCat.{u}) ≤
      Underlying.fibrations (forget GrpCat) := sorry

/-- 08P0 (Lemma 14.31.7), at the categorical owner layer: an epimorphism of simplicial groups
induces a Kan fibration of underlying simplicial sets. -/
@[stacks 08P0 "simplicial-group epimorphisms are underlying Kan fibrations"]
instance fibration {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y) [Epi f] :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := sorry

namespace fibration

/-- 08P0 (Lemma 14.31.7), in concrete form: a degreewise-surjective simplicial-group morphism
induces a Kan fibration of underlying simplicial sets. -/
@[stacks 08P0 "degreewise-surjective simplicial-group Kan fibrations"]
theorem of_surjective {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y)
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := sorry

end fibration

end underlying

end CategoryTheory.SimplicialObject.Grp

namespace CategoryTheory.SimplicialObject.AddGrp

namespace underlying

/-- The underlying simplicial set of a simplicial additive group is a Kan complex. -/
@[stacks 08NZ "simplicial additive groups are Kan complexes"]
instance kanComplex (X : SimplicialObject AddGrpCat.{u}) :
    SSet.KanComplex (X ⋙ forget AddGrpCat) := sorry

/-- Degreewise surjectivity characterizes epimorphisms of simplicial additive groups. -/
@[stacks 08P0 "degreewise-surjective epimorphisms of simplicial additive groups"]
theorem epi_iff_surjective {X Y : SimplicialObject AddGrpCat.{u}} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n) := sorry

/-- Epimorphisms of simplicial additive groups induce underlying Kan fibrations. -/
@[stacks 08P0 "epimorphisms of simplicial additive groups induce Kan fibrations"]
theorem epimorphisms_le_fibrations :
    MorphismProperty.epimorphisms (SimplicialObject AddGrpCat.{u}) ≤
      Underlying.fibrations (forget AddGrpCat) := sorry

/-- An epimorphism of simplicial additive groups induces a Kan fibration of underlying
simplicial sets. -/
@[stacks 08P0 "simplicial-additive-group epimorphisms are underlying Kan fibrations"]
instance fibration {X Y : SimplicialObject AddGrpCat.{u}} (f : X ⟶ Y) [Epi f] :
    Fibration (Functor.whiskerRight f (forget AddGrpCat)) := sorry

namespace fibration

/-- A degreewise-surjective simplicial-additive-group morphism induces a Kan fibration. -/
@[stacks 08P0 "degreewise-surjective simplicial-additive-group Kan fibrations"]
theorem of_surjective {X Y : SimplicialObject AddGrpCat.{u}} (f : X ⟶ Y)
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget AddGrpCat)) := sorry

end fibration

end underlying

end CategoryTheory.SimplicialObject.AddGrp

namespace CategoryTheory.SimplicialObject.CommGrp

namespace underlying

/-- The underlying simplicial set of a simplicial commutative group is a Kan complex. -/
@[stacks 08NZ "simplicial commutative groups are Kan complexes"]
instance kanComplex (X : SimplicialObject CommGrpCat.{u}) :
    SSet.KanComplex (X ⋙ forget CommGrpCat) := sorry

/-- Degreewise surjectivity characterizes epimorphisms of simplicial commutative groups. -/
@[stacks 08P0 "degreewise-surjective epimorphisms of simplicial commutative groups"]
theorem epi_iff_surjective {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n) := sorry

/-- Epimorphisms of simplicial commutative groups induce underlying Kan fibrations. -/
@[stacks 08P0 "epimorphisms of simplicial commutative groups induce Kan fibrations"]
theorem epimorphisms_le_fibrations :
    MorphismProperty.epimorphisms (SimplicialObject CommGrpCat.{u}) ≤
      Underlying.fibrations (forget CommGrpCat) := sorry

/-- An epimorphism of simplicial commutative groups induces a Kan fibration of underlying
simplicial sets. -/
@[stacks 08P0 "simplicial-commutative-group epimorphisms are underlying Kan fibrations"]
instance fibration {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y) [Epi f] :
    Fibration (Functor.whiskerRight f (forget CommGrpCat)) := sorry

namespace fibration

/-- A degreewise-surjective simplicial-commutative-group morphism induces a Kan fibration. -/
@[stacks 08P0 "degreewise-surjective simplicial-commutative-group Kan fibrations"]
theorem of_surjective {X Y : SimplicialObject CommGrpCat.{u}} (f : X ⟶ Y)
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget CommGrpCat)) := sorry

end fibration

end underlying

end CategoryTheory.SimplicialObject.CommGrp

namespace CategoryTheory.SimplicialObject.AddCommGrp

namespace underlying

/-- The underlying simplicial set of a simplicial abelian group is a Kan complex. -/
@[stacks 08NZ "simplicial abelian groups are Kan complexes"]
instance kanComplex (X : SimplicialObject AddCommGrpCat.{u}) :
    SSet.KanComplex (X ⋙ forget AddCommGrpCat) := sorry

/-- Degreewise surjectivity characterizes epimorphisms of simplicial abelian groups. -/
@[stacks 08P0 "degreewise-surjective epimorphisms of simplicial abelian groups"]
theorem epi_iff_surjective {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) :
    Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n) := sorry

/-- Epimorphisms of simplicial abelian groups lie in the morphism property detected by underlying
Kan fibrations. -/
@[stacks 08P0 "epimorphisms of simplicial abelian groups induce Kan fibrations"]
theorem epimorphisms_le_fibrations :
    MorphismProperty.epimorphisms (SimplicialObject AddCommGrpCat.{u}) ≤
      Underlying.fibrations (forget AddCommGrpCat) := sorry

/-- An epimorphism of simplicial abelian groups induces a Kan fibration of underlying simplicial
sets. -/
@[stacks 08P0 "simplicial-abelian-group epimorphisms are underlying Kan fibrations"]
instance fibration {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y) [Epi f] :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

namespace fibration

/-- The degreewise-surjective specialization for simplicial abelian groups. -/
@[stacks 08P0 "degreewise-surjective simplicial-abelian-group Kan fibrations"]
theorem of_surjective
    {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)
    (hsurjective : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := sorry

end fibration

end underlying

end CategoryTheory.SimplicialObject.AddCommGrp
