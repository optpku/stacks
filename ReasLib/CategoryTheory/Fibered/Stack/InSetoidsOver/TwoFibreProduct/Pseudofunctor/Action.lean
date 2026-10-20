module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.TwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Pseudofunctor.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Action of the two-fibre-product pseudofunctor on stacks in setoids

This leaf owns the direct `1`-cell, `2`-cell, and local Hom actions. It also exposes their
groupoid-stack and underlying-functor readouts for downstream computations.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Setoids.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- The direct action of setoid-stack two-fibre products on a bundled cospan morphism. -/
@[stacks 0434 "setoid-stack two-fibre-product map action"]
noncomputable def map (psi : S ⟶ T) :
    (pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T :=
  Bicategory.InducedBicategory.mkHom ((ambientPseudofunctor J).map psi)

/-- The direct action of setoid-stack two-fibre products on a bundled cospan `2`-morphism. -/
@[stacks 0434 "setoid-stack two-fibre-product two-cell action"]
noncomputable def map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    map psi ⟶ map phi :=
  Bicategory.InducedBicategory.mkHom₂ ((ambientPseudofunctor J).map₂ Gamma)

/-- The direct action on cospan `2`-cells preserves identity morphisms. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product two-cell identity"]
theorem map₂.id (psi : S ⟶ T) :
    map₂ (𝟙 psi) = 𝟙 (map psi) := sorry

/-- The direct action on cospan `2`-cells preserves vertical composition. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product two-cell composition"]
theorem map₂.comp {psi phi chi : S ⟶ T}
    (Gamma : psi ⟶ phi) (Delta : phi ⟶ chi) :
    map₂ (Gamma ≫ Delta) = map₂ Gamma ≫ map₂ Delta := sorry

/-- The direct local Hom functor of setoid-stack two-fibre products between two bundled cospans. -/
@[stacks 0434 "setoid-stack two-fibre-product local Hom functor"]
noncomputable def mapFunctor (S T : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (S ⟶ T) ⥤ ((pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T) :=
  { obj := map
    map := map₂
    map_id := map₂.id
    map_comp := map₂.comp }

/-- The object action of the bundled-cospan pseudofunctor is the canonical setoid-stack
two-fibre-product apex. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product object computation"]
theorem pseudofunctor.obj (S : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).obj S = apex S.fst S.snd := sorry

/-- Forgetting the thin-fibre condition from the direct map recovers the canonical map of the
componentwise-forgotten groupoid-stack cospan. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product map groupoid readout"]
theorem map.hom (psi : S ⟶ T) :
    (map psi).hom =
      StackOver.Groupoids.TwoFibreProduct.map
        ((Bicategory.Cospan.map
          (StackOver.Setoids.forget J).toPseudofunctor).map psi) := sorry

/-- The groupoid-stack morphism underlying the direct setoid-stack map is the ambient
pseudofunctor action. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product map ambient readout"]
theorem map.toAmbient (psi : S ⟶ T) :
    (map psi).hom = (ambientPseudofunctor J).map psi := sorry

/-- Forgetting the pseudofunctor `1`-cell action recovers its ambient groupoid-stack action. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product pseudofunctor map ambient readout"]
theorem pseudofunctor.map.toAmbient (psi : S ⟶ T) :
    ((pseudofunctor J).map psi).hom =
      (ambientPseudofunctor J).map psi := sorry

/-- The based functor underlying the direct map is the based functor of its ambient
groupoid-stack action; heterogeneous equality accounts only for the proof-bearing endpoint
presentation. -/
@[stacks 0434 "setoid-stack two-fibre-product based-functor readout"]
theorem map.toBasedFunctor (psi : S ⟶ T) :
    StackOver.Setoids.Hom.toBasedFunctor (map psi) ≍
      StackOver.Groupoids.Hom.toBasedFunctor
        ((ambientPseudofunctor J).map psi) := sorry

/-- The total functor underlying the direct map is the total functor of its ambient
groupoid-stack action. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product total-functor readout"]
theorem map.toFunctor (psi : S ⟶ T) :
    StackOver.Setoids.Hom.toFunctor (map psi) =
      StackOver.Groupoids.Hom.toFunctor
        ((ambientPseudofunctor J).map psi) := sorry

/-- The ambient groupoid-stack `2`-cell underlying the direct setoid-stack action.  This owner
encapsulates the endpoint identifications introduced by the full-subbicategory lift. -/
@[stacks 0434 "setoid-stack two-fibre-product ambient two-cell owner"]
noncomputable def map₂.toAmbient
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    StackOver.Setoids.Hom.toGroupoidsMor (map psi) ⟶
      StackOver.Setoids.Hom.toGroupoidsMor (map phi) :=
  (ambientPseudofunctor J).map₂ Gamma

/-- Forgetting the direct `2`-cell action gives its named ambient groupoid-stack owner;
heterogeneous equality records the proof-bearing endpoint identification. -/
@[stacks 0434 "setoid-stack two-fibre-product two-cell ambient readout"]
theorem map₂.hom
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (map₂ Gamma).hom ≍ map₂.toAmbient Gamma := sorry

/-- The pseudofunctor `2`-cell field is the direct public action; heterogeneous equality
accounts only for its dependent endpoints. -/
@[stacks 0434 "setoid-stack two-fibre-product pseudofunctor two-cell readout"]
theorem pseudofunctor.map₂
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (pseudofunctor J).map₂ Gamma ≍ map₂ Gamma := sorry

/-- The pseudofunctor `1`-cell field is the direct public setoid-stack map. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product pseudofunctor map computation"]
theorem pseudofunctor.map (psi : S ⟶ T) :
    (pseudofunctor J).map psi = map psi := sorry

/-- The pseudofunctor local action is the direct public two-fibre-product Hom functor. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product pseudofunctor Hom computation"]
theorem pseudofunctor.mapFunctor (S T : Bicategory.Cospan
    (StackOver.Setoids.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).mapFunctor S T = mapFunctor S T := sorry

/-- The object action of the direct local Hom functor is the public map. -/
@[simp, stacks 0434 "setoid-stack two-fibre-product Hom object computation"]
theorem mapFunctor.obj (psi : S ⟶ T) :
    (mapFunctor S T).obj psi = map psi := sorry

/-- The morphism action of the direct local Hom functor is `map₂`; heterogeneous equality
accounts only for dependent endpoints. -/
@[stacks 0434 "setoid-stack two-fibre-product Hom two-cell readout"]
theorem mapFunctor.map
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    (mapFunctor S T).map Gamma ≍ map₂ Gamma := sorry

end StackOver.Setoids.TwoFibreProduct

end CategoryTheory
