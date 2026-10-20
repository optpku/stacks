module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Cotensor.Base
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotensor functoriality in the cosimplicial object

This leaf owns maps and the endofunctor obtained by fixing the simplicial-set index.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

namespace cotensor

variable (U : SSet.{w}) {V W : CosimplicialObject C}

/-- The raw component induced on cotensors by a morphism of cosimplicial objects. -/
@[stacks 019V "cotensor induced component"]
abbrev homApp [HasCotensor U V] [HasCotensor U W]
    (f : V ⟶ W) (n : SimplexCategory) :
    (cotensor U V).obj n ⟶ (cotensor U W).obj n :=
  Functor.indexedProd.op.homApp U f n

/-- The raw components induced by a morphism of cosimplicial objects form a natural family. -/
@[stacks 019V "cotensor induced naturality"]
theorem homApp.naturality [HasCotensor U V] [HasCotensor U W]
    (f : V ⟶ W) {m n : SimplexCategory} (g : m ⟶ n) :
    (cotensor U V).map g ≫ homApp U f n = homApp U f m ≫ (cotensor U W).map g := sorry

/-- A morphism of cosimplicial objects induces a morphism between their cotensors by `U`. -/
@[stacks 019V "cotensor induced morphism"]
abbrev hom [HasCotensor U V] [HasCotensor U W]
    (f : V ⟶ W) : cotensor U V ⟶ cotensor U W :=
  Functor.indexedProd.op.hom U f

/-- The degreewise component of the morphism induced between cotensors. -/
@[simp, stacks 019V "cotensor induced component formula"]
theorem hom_app [HasCotensor U V] [HasCotensor U W]
    (f : V ⟶ W) (n : SimplexCategory) :
    (hom U f).app n = homApp U f n := sorry

/-- Evaluation of `hom U f` at a product factor. -/
@[reassoc (attr := simp), stacks 019V "cotensor induced projection formula"]
theorem hom.π
    [HasCotensor U V] [HasCotensor U W] (f : V ⟶ W)
    (n : SimplexCategory) (u : U.obj (op n)) :
    (hom U f).app n ≫ Pi.π (fun _ : U.obj (op n) ↦ W.obj n) u =
      Pi.π (fun _ : U.obj (op n) ↦ V.obj n) u ≫ f.app n := sorry

/-- Cotensoring the identity morphism gives the identity morphism. -/
@[simp, stacks 019V "cotensor induced identity"]
theorem hom.id (V : CosimplicialObject C) [HasCotensor U V] :
    hom U (𝟙 V) = 𝟙 (cotensor U V) := sorry

/-- Cotensoring preserves composition. -/
@[stacks 019V "cotensor induced composition"]
theorem hom.comp {V W X : CosimplicialObject C}
    [HasCotensor U V] [HasCotensor U W] [HasCotensor U X]
    (f : V ⟶ W) (g : W ⟶ X) :
    hom U (f ≫ g) = hom U f ≫ hom U g := sorry

end cotensor

section ObjectVariableFunctor

variable (U : SSet.{w})
variable [HasCotensors U C]

/-- Cotensoring by `U` as a functor of the cosimplicial-object variable. -/
@[stacks 019V "cotensor functoriality"]
abbrev cotensor.functor : CosimplicialObject C ⥤ CosimplicialObject C :=
  Functor.indexedProd.op.functor U

/-- The object part of `cotensor.functor U` is cotensoring by `U`. -/
@[simp, stacks 019V "cotensor functor object formula"]
theorem cotensor.functor.obj (V : CosimplicialObject C) :
    (cotensor.functor (C := C) U).obj V = cotensor U V := sorry

/-- The map part of `cotensor.functor U` is the canonical map in the cosimplicial-object
variable. -/
@[simp, stacks 019V "cotensor functor map formula"]
theorem cotensor.functor.map {V W : CosimplicialObject C} (f : V ⟶ W) :
    (cotensor.functor (C := C) U).map f = cotensor.hom U f := sorry

end ObjectVariableFunctor

end CategoryTheory.CosimplicialObject
