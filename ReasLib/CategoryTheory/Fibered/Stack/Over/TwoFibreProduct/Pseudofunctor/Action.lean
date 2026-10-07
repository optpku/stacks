module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoFibreProduct.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Over.TwoCell

/-!
# Action of the two-fibre-product pseudofunctor on stacks

This leaf exposes the object, `1`-cell, `2`-cell, and local Hom actions used by downstream stack
arguments.  Ambient readouts make it possible to reuse the computation API of
`FiberedCategoryOver.TwoFibreProduct.pseudofunctor` without unfolding the stack lift.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.TwoFibreProduct

variable {S T : Bicategory.Cospan
  (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)}

/-- The action of stack-valued two-fibre products on a bundled cospan morphism. -/
@[stacks 026G "stack two-fibre-product map action"]
noncomputable def map (psi : S ⟶ T) :
    (pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T :=
  Bicategory.InducedBicategory.mkHom ((ambientPseudofunctor J).map psi)

/-- The action of stack-valued two-fibre products on a bundled cospan `2`-morphism. -/
@[stacks 026G "stack two-fibre-product two-cell action"]
noncomputable def map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    map psi ⟶ map phi :=
  Bicategory.InducedBicategory.mkHom₂ ((ambientPseudofunctor J).map₂ Gamma)

/-- The ambient object action is the neutral two-fibre product of the componentwise-forgotten
cospan legs. -/
@[simp, stacks 026G "ambient stack two-fibre-product object computation"]
theorem ambientPseudofunctor.obj
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (ambientPseudofunctor J).obj S =
      FiberedCategoryOver.TwoFibreProduct.apex
        ((StackOver.forget J).map S.fst) ((StackOver.forget J).map S.snd) := sorry

/-- Forgetting the stack witness from the object action recovers the ambient object action. -/
@[simp, stacks 026G "stack two-fibre-product ambient object readout"]
theorem pseudofunctor.obj.toFiberedCategoryOver
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    ((pseudofunctor J).obj S).toFiberedCategoryOver =
      (ambientPseudofunctor J).obj S := sorry

/-- The object action of the bundled-cospan pseudofunctor is the canonical stack-valued
two-fibre-product apex. -/
@[simp, stacks 026G "stack two-fibre-product object computation"]
theorem pseudofunctor.obj
    (S : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).obj S = apex S.fst S.snd := sorry

/-- The ambient `1`-cell action is the neutral two-fibre-product map of the
componentwise-forgotten cospan morphism. -/
@[simp, stacks 026G "ambient stack two-fibre-product map computation"]
theorem ambientPseudofunctor.map (psi : S ⟶ T) :
    (ambientPseudofunctor J).map psi =
      (FiberedCategoryOver.TwoFibreProduct.pseudofunctor (C := C)).map
        ((Bicategory.Cospan.map
          (StackOver.forget J).toPseudofunctor).map psi) := sorry

/-- Forgetting the stack condition from the public `1`-cell action recovers the ambient
pseudofunctor action. -/
@[simp, stacks 026G "stack two-fibre-product map ambient readout"]
theorem map.hom (psi : S ⟶ T) :
    StackOver.Hom.toMor (map psi) =
      (ambientPseudofunctor J).map psi := sorry

/-- The ambient `2`-cell underlying the public action.  This owner encapsulates the endpoint
identifications introduced by the full-subbicategory lift. -/
@[stacks 026G "ambient stack two-fibre-product two-cell owner"]
noncomputable def map₂.toAmbient
    {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    StackOver.Hom.toMor (map psi) ⟶ StackOver.Hom.toMor (map phi) :=
  (ambientPseudofunctor J).map₂ Gamma

/-- Forgetting the stack condition from the public `2`-cell action gives its named ambient
owner. -/
@[simp, stacks 026G "stack two-fibre-product two-cell ambient readout"]
theorem map₂.hom {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    StackOver.Hom.toMor₂ (map₂ Gamma) = map₂.toAmbient Gamma := sorry

/-- The pseudofunctor `1`-cell field is the public stack-valued two-fibre-product map. -/
@[simp, stacks 026G "stack two-fibre-product pseudofunctor map computation"]
theorem pseudofunctor.map (psi : S ⟶ T) :
    (pseudofunctor J).map psi = map psi := sorry

/-- The pseudofunctor `2`-cell field is the public stack-valued two-fibre-product action.  The
heterogeneous equality keeps the definitionally equal full-subbicategory endpoints opaque. -/
@[simp, stacks 026G "stack two-fibre-product pseudofunctor two-cell computation"]
theorem pseudofunctor.map₂ {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    HEq ((pseudofunctor J).map₂ Gamma) (map₂ Gamma) := sorry

/-- The public `2`-cell action preserves identity `2`-morphisms. -/
@[simp, stacks 026G "stack two-fibre-product two-cell identity"]
theorem map₂.id (psi : S ⟶ T) :
    map₂ (𝟙 psi) = 𝟙 (map psi) := sorry

/-- The public `2`-cell action preserves vertical composition. -/
@[simp, stacks 026G "stack two-fibre-product two-cell composition"]
theorem map₂.comp {psi phi chi : S ⟶ T}
    (Gamma : psi ⟶ phi) (Delta : phi ⟶ chi) :
    map₂ (Gamma ≫ Delta) = map₂ Gamma ≫ map₂ Delta := sorry

/-- The local Hom functor of stack-valued two-fibre products between two bundled cospans.  Its
object and morphism data are the public `map` and `map₂`; only the functor laws are propositional
coherence. -/
@[stacks 026G "stack two-fibre-product local Hom functor"]
noncomputable def mapFunctor (S T : Bicategory.Cospan
    (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (S ⟶ T) ⥤ ((pseudofunctor J).obj S ⟶ (pseudofunctor J).obj T) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- The pseudofunctor local action is the public two-fibre-product Hom functor. -/
@[simp, stacks 026G "stack two-fibre-product pseudofunctor Hom computation"]
theorem pseudofunctor.mapFunctor
    (S T : Bicategory.Cospan
      (StackOver.{u, v, max w (max u (max v vB)), max v vB} J)) :
    (pseudofunctor J).mapFunctor S T = mapFunctor S T := sorry

/-- The object action of the local Hom functor is the public two-fibre-product map. -/
@[simp, stacks 026G "stack two-fibre-product Hom object computation"]
theorem mapFunctor.obj (psi : S ⟶ T) :
    (mapFunctor S T).obj psi = map psi := sorry

/-- The morphism action of the local Hom functor is the public two-fibre-product `2`-cell map. -/
@[simp, stacks 026G "stack two-fibre-product Hom two-cell computation"]
theorem mapFunctor.map {psi phi : S ⟶ T} (Gamma : psi ⟶ phi) :
    HEq ((mapFunctor S T).map Gamma) (map₂ Gamma) := sorry

end StackOver.TwoFibreProduct

end CategoryTheory
