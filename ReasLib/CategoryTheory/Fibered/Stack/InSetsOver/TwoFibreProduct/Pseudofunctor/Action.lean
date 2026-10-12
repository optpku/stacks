/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Action of the two-fibre-product pseudofunctor on stacks in sets

This leaf owns direct `1`-cell, `2`-cell, and local Hom actions. Forgetful and neutral readouts
are separated into `Action.Computations`.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- The direct action of set-stack two-fibre products on a bundled cospan morphism. -/
@[stacks 0434 "set-stack two-fibre-product map action"]
noncomputable def map (psi : S ⟶ T) :
    (pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T :=
  Bicategory.InducedBicategory.mkHom ((ambientPseudofunctor J).map psi)

/-- The direct action of set-stack two-fibre products on a bundled cospan `2`-morphism. -/
@[stacks 0434 "set-stack two-fibre-product two-cell action"]
noncomputable def map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    map psi ⟶ map phi :=
  Bicategory.InducedBicategory.mkHom₂ ((ambientPseudofunctor J).map₂ Gamma)

/-- The direct action on cospan `2`-cells preserves identities. -/
@[simp, stacks 0434 "set-stack two-fibre-product two-cell identity"]
theorem map₂.id (psi : S ⟶ T) :
    map₂ (𝟙 psi) = 𝟙 (map psi) := sorry

/-- The direct action on cospan `2`-cells preserves vertical composition. -/
@[simp, stacks 0434 "set-stack two-fibre-product two-cell composition"]
theorem map₂.comp {psi phi chi : S ⟶ T}
    (Gamma : psi ⟶ phi) (Delta : phi ⟶ chi) :
    map₂ (Gamma ≫ Delta) = map₂ Gamma ≫ map₂ Delta := sorry

/-- The direct local Hom functor of set-stack two-fibre products. -/
@[stacks 0434 "set-stack two-fibre-product local Hom functor"]
noncomputable def mapFunctor (S T : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (S ⟶ T) ⥤ ((pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T) :=
  { obj := map
    map := map₂
    map_id := map₂.id
    map_comp := map₂.comp }

/-- The object action is the canonical two-fibre-product apex of stacks in sets. -/
@[simp, stacks 0434 "set-stack two-fibre-product object action"]
theorem pseudofunctor.obj (S : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).obj S = apex S.fst S.snd := sorry

/-- Forgetting the discrete-fibration condition from the direct map recovers the canonical map
of the componentwise-forgotten setoid-stack cospan. -/
@[simp, stacks 0434 "set-stack two-fibre-product ambient map readout"]
theorem map.hom (psi : S ⟶ T) :
    (map psi).hom =
      StackOver.Setoids.TwoFibreProduct.map
        ((Bicategory.Cospan.map
          (StackOver.Sets.forget J).toPseudofunctor).map psi) := sorry

/-- The pseudofunctor `1`-cell field is the direct public set-stack map. -/
@[simp, stacks 0434 "set-stack two-fibre-product pseudofunctor map readout"]
theorem pseudofunctor.map (psi : S ⟶ T) :
    (pseudofunctor J).map psi = map psi := sorry

/-- The pseudofunctor `2`-cell field is the direct public set-stack `2`-cell action.
Heterogeneous equality accounts only for the proof-bearing full-sub endpoints. -/
@[stacks 0434 "set-stack two-fibre-product pseudofunctor two-cell readout"]
theorem pseudofunctor.map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor J).map₂ Gamma ≍ map₂ Gamma := sorry

/-- The pseudofunctor local action is the direct public Hom functor. -/
@[simp, stacks 0434 "set-stack two-fibre-product Hom action readout"]
theorem pseudofunctor.mapFunctor (S T : Bicategory.Cospan
    (StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).mapFunctor S T = mapFunctor S T := sorry

/-- The object action of the direct local Hom functor is `map`. -/
@[simp, stacks 0434 "set-stack two-fibre-product Hom object readout"]
theorem mapFunctor.obj (psi : S ⟶ T) :
    (mapFunctor S T).obj psi = map psi := sorry

/-- The morphism action of the direct local Hom functor is `map₂`; heterogeneous equality
accounts only for proof-bearing endpoints. -/
@[stacks 0434 "set-stack two-fibre-product Hom two-cell readout"]
theorem mapFunctor.map {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (mapFunctor S T).map Gamma ≍ map₂ Gamma := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
