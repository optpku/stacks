/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Action of the two-fibre-product pseudofunctor on groupoid stacks

This leaf identifies the lifted object, `1`-cell, `2`-cell, and local Hom action with the
corresponding neutral two-fibre-product operations after componentwise stack forgetting.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Groupoids.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- The action of stack-valued two-fibre products on a bundled cospan morphism. -/
@[stacks 02ZL "two-fibre-product pseudofunctor map on stack cospans"]
noncomputable def map (psi : S ⟶ T) :
    (pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T :=
  Bicategory.InducedBicategory.mkHom ((ambientPseudofunctor J).map psi)

/-- The action of stack-valued two-fibre products on a bundled cospan `2`-morphism. -/
@[stacks 02ZL "two-fibre-product pseudofunctor 2-cell action"]
noncomputable def map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    map psi ⟶ map phi :=
  Bicategory.InducedBicategory.mkHom₂ ((ambientPseudofunctor J).map₂ Gamma)

/-- The direct action on cospan `2`-cells preserves identity morphisms. -/
@[simp, stacks 02ZL "identity law for two-fibre-product 2-cell action"]
theorem map₂.id (psi : S ⟶ T) :
    map₂ (𝟙 psi) = 𝟙 (map psi) := sorry

/-- The direct action on cospan `2`-cells preserves vertical composition. -/
@[simp, stacks 02ZL "composition law for two-fibre-product 2-cell action"]
theorem map₂.comp {psi phi chi : S ⟶ T}
    (Gamma : psi ⟶ phi) (Delta : phi ⟶ chi) :
    map₂ (Gamma ≫ Delta) = map₂ Gamma ≫ map₂ Delta := sorry

/-- The local Hom functor of stack-valued two-fibre products between two bundled cospans. -/
@[stacks 02ZL "local Hom functor for stack two-fibre products"]
noncomputable def mapFunctor (S T : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (S ⟶ T) ⥤ ((pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T) :=
  { obj := map
    map := map₂
    map_id := map₂.id
    map_comp := map₂.comp }

/-- The object action of the bundled-cospan pseudofunctor is the canonical stack-valued
two-fibre-product apex. -/
@[simp, stacks 02ZL "object action of the groupoid-stack two-fibre-product pseudofunctor"]
theorem pseudofunctor.obj (S : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).obj S = apex S.fst S.snd := sorry

/-- Forgetting the stack condition from the `1`-cell action recovers the neutral explicit
two-fibre-product map of the componentwise-forgotten cospan transformation. -/
@[simp, stacks 02ZL "ambient map readout for stack two-fibre products"]
theorem map.hom (psi : S ⟶ T) :
    (map psi).hom =
      CategoryTheory.TwoFibreProduct.map
        (Bicategory.Cospan.Hom.toCospanTransform
          ((Bicategory.Cospan.map
            (StackOver.Groupoids.forget J).toPseudofunctor).map psi)) := sorry

/-- The groupoid-fibred morphism underlying the direct stack-valued map is the ambient
pseudofunctor action. -/
@[simp, stacks 02ZL "ambient action readout for stack two-fibre-product maps"]
theorem map.toAmbient (psi : S ⟶ T) :
    (map psi).hom = (ambientPseudofunctor J).map psi := sorry

/-- The groupoid-fibred morphism underlying the pseudofunctor action is its ambient action. -/
@[simp, stacks 02ZL "ambient action readout for the lifted pseudofunctor"]
theorem pseudofunctor.map.toAmbient (psi : S ⟶ T) :
    ((pseudofunctor J).map psi).hom =
      (ambientPseudofunctor J).map psi := sorry

/-- The based functor underlying the stack-valued two-fibre-product map is the based functor of
the neutral explicit map. -/
@[simp, stacks 02ZL "based-functor readout for stack two-fibre-product maps"]
theorem map.toBasedFunctor (psi : S ⟶ T) :
    StackOver.Groupoids.Hom.toBasedFunctor (map psi) =
      FiberedCategoryOver.Groupoids.toBasedFunctor
        (CategoryTheory.TwoFibreProduct.map
          (Bicategory.Cospan.Hom.toCospanTransform
            ((Bicategory.Cospan.map
              (StackOver.Groupoids.forget J).toPseudofunctor).map psi))) := sorry

/-- The total functor underlying the stack-valued two-fibre-product map is the total functor of
the neutral explicit map. -/
@[simp, stacks 02ZL "total-functor readout for stack two-fibre-product maps"]
theorem map.toFunctor (psi : S ⟶ T) :
    StackOver.Groupoids.Hom.toFunctor (map psi) =
      FiberedCategoryOver.Groupoids.toFunctor
        (CategoryTheory.TwoFibreProduct.map
          (Bicategory.Cospan.Hom.toCospanTransform
            ((Bicategory.Cospan.map
              (StackOver.Groupoids.forget J).toPseudofunctor).map psi))) := sorry

/-- Forgetting the stack condition from the direct `2`-cell action gives the ambient
two-fibre-product action; heterogeneous equality accounts only for dependent endpoints. -/
@[stacks 02ZL "ambient 2-cell readout for stack two-fibre products"]
theorem map₂.hom
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (map₂ Gamma).hom ≍ (ambientPseudofunctor J).map₂ Gamma := sorry

/-- The pseudofunctor `2`-cell field is the direct public action; heterogeneous equality
accounts only for dependent endpoints. -/
@[stacks 02ZL "public 2-cell action readout for stack two-fibre products"]
theorem pseudofunctor.map₂
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor J).map₂ Gamma ≍ map₂ Gamma := sorry

/-- The pseudofunctor `1`-cell field is the public stack-valued two-fibre-product map. -/
@[simp, stacks 02ZL "public map readout for stack two-fibre products"]
theorem pseudofunctor.map (psi : S ⟶ T) :
    (pseudofunctor J).map psi = map psi := sorry

/-- The pseudofunctor local action is the public two-fibre-product Hom functor. -/
@[simp, stacks 02ZL "public local Hom readout for stack two-fibre products"]
theorem pseudofunctor.mapFunctor (S T : Bicategory.Cospan
    (StackOver.Groupoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).mapFunctor S T = mapFunctor S T := sorry

/-- The object action of the local Hom functor is the public two-fibre-product map. -/
@[simp, stacks 02ZL "object readout for the stack two-fibre-product Hom functor"]
theorem mapFunctor.obj (psi : S ⟶ T) :
    (mapFunctor S T).obj psi = map psi := sorry

/-- The morphism action of the public local Hom functor is `map₂`; heterogeneous equality
accounts only for dependent endpoints. -/
@[stacks 02ZL "morphism readout for the stack two-fibre-product Hom functor"]
theorem mapFunctor.map
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (mapFunctor S T).map Gamma ≍ map₂ Gamma := sorry

end StackOver.Groupoids.TwoFibreProduct

end CategoryTheory
