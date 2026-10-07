module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.HomFamily
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Universe-lifted coyoneda-indexed products

This leaf is the cross-universe product-side companion of
`Functor.indexedCoprod.uliftYoneda`. It keeps the index universe independent from the category of
values while exposing the same compatible-family, evaluation, variance, and representability API
as the plain `indexedProd.coyoneda` owner.

The opposite-oriented product owner remains in `IndexedProduct.Op`; this file deliberately owns
only the ordinary presheaf orientation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {E : Type i} [Category.{d} E]
variable {C : Type u} [Category.{v} C]

namespace indexedProd.uliftCoyoneda

variable (e : E)

namespace HomFamily

/-- Evaluate a compatible family indexed by `uliftCoyoneda.obj (op e)` at the lifted identity. -/
@[stacks 017M "lifted coyoneda identity evaluation"]
def eval {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedProd.HomFamily.Compatible
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X)) :
    V.obj (op e) ⟶ X :=
  F.1 (op e) (ULift.up (𝟙 e))

/-- The lifted identity is the selected component of a compatible family. -/
@[simp, stacks 017M "lifted coyoneda identity-evaluation formula"]
theorem eval.apply {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedProd.HomFamily.Compatible
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X)) :
    eval e F = F.1 (op e) (ULift.up (𝟙 e)) := sorry

/-- A map at the representing object induces a lifted coyoneda-indexed family. -/
@[stacks 017M "family induced by a lifted coyoneda map"]
def ofMap (V : Eᵒᵖ ⥤ C) {X : C} (f : V.obj (op e) ⟶ X) :
    indexedProd.HomFamily
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X) :=
  fun Delta g ↦ V.map (Opposite.op g.down) ≫ f

/-- Compute a component of a family induced by a map at the representing object. -/
@[simp, stacks 017M "lifted coyoneda induced-family component"]
theorem ofMap.apply (V : Eᵒᵖ ⥤ C) {X : C} (f : V.obj (op e) ⟶ X)
    (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta)) :
    ofMap e V f Delta g = V.map (Opposite.op g.down) ≫ f := sorry

/-- The family induced by a representing-object map is compatible. -/
@[stacks 017M "compatibility of a lifted coyoneda family"]
theorem ofMap.isCompatible (V : Eᵒᵖ ⥤ C) {X : C}
    (f : V.obj (op e) ⟶ X) :
    (ofMap e V f).IsCompatible := sorry

/-- Package the induced lifted coyoneda family with its compatibility proof. -/
@[stacks 017M "compatible lifted coyoneda family induced at the representing object"]
def ofMap.compatible (V : Eᵒᵖ ⥤ C) {X : C}
    (f : V.obj (op e) ⟶ X) :
    indexedProd.HomFamily.Compatible
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X) :=
  ⟨ofMap e V f, ofMap.isCompatible e V f⟩

/-- Compute a component of a packaged induced lifted coyoneda family. -/
@[simp, stacks 017M "compatible lifted coyoneda family component"]
theorem ofMap.compatible.apply (V : Eᵒᵖ ⥤ C) {X : C}
    (f : V.obj (op e) ⟶ X) (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta)) :
    (ofMap.compatible e V f).1 Delta g = V.map (Opposite.op g.down) ≫ f := sorry

/-- Reconstructing a compatible lifted coyoneda family from its identity value is the identity. -/
@[stacks 017M "lifted coyoneda family reconstruction"]
theorem ofMap.compatible_eval {X : C} (V : Eᵒᵖ ⥤ C)
    (F : indexedProd.HomFamily.Compatible
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X)) :
    ofMap.compatible e V (eval e F) = F := sorry

/-- Evaluating the family induced by a representing-object map returns that map. -/
@[stacks 017M "lifted coyoneda family evaluation law"]
theorem eval_ofMap {X : C} (V : Eᵒᵖ ⥤ C)
    (f : V.obj (op e) ⟶ X) :
    eval e (ofMap.compatible e V f) = f := sorry

/-- Compatible lifted coyoneda families are canonically maps from the representing value. -/
@[stacks 017M "lifted coyoneda compatible-family equivalence"]
def evalEquiv (V : Eᵒᵖ ⥤ C) (X : C) :
    indexedProd.HomFamily.Compatible
        (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X) ≃
      (V.obj (op e) ⟶ X) where
  toFun := eval e
  invFun := ofMap.compatible e V
  left_inv := ofMap.compatible_eval e V
  right_inv := eval_ofMap e V

/-- The forward map of the lifted coyoneda family equivalence is identity evaluation. -/
@[simp, stacks 017M "lifted coyoneda family equivalence forward formula"]
theorem evalEquiv.apply {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedProd.HomFamily.Compatible
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e)) V ((Functor.const Eᵒᵖ).obj X)) :
    evalEquiv e V X F = eval e F := sorry

/-- The inverse of the lifted coyoneda family equivalence is induced by the selected map. -/
@[simp, stacks 017M "lifted coyoneda family equivalence inverse formula"]
theorem evalEquiv.symm_apply {X : C} (V : Eᵒᵖ ⥤ C)
    (f : V.obj (op e) ⟶ X) :
    (evalEquiv e V X).symm f = ofMap.compatible e V f := sorry

end HomFamily

/-- Maps into a lifted coyoneda-indexed product of a constant diagram are maps from the
corresponding value of the source presheaf to the constant factor. -/
@[stacks 017M "lifted coyoneda-indexed product Hom equivalence"]
def homEquiv (X : C)
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C) :
    (V ⟶ indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
        ((Functor.const Eᵒᵖ).obj X)) ≃
      (V.obj (op e) ⟶ X) :=
  (indexedProd.HomFamily.homEquiv
      (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      V ((Functor.const Eᵒᵖ).obj X)).trans
    (HomFamily.evalEquiv e V X)

/-- Transport the lifted coyoneda equivalence across an isomorphism of indexing functors. -/
@[stacks 017M "lifted coyoneda Hom equivalence up to index isomorphism"]
def homEquiv.ofIso {U : E ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftCoyoneda.{w}.obj (op e)) (X : C)
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C) :
    (V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) ≃
      (V.obj (op e) ⟶ X) :=
  ((indexedProd.HomFamily.homEquiv U V ((Functor.const Eᵒᵖ).obj X)).trans
      (indexedProd.HomFamily.restrictEquiv a
        V ((Functor.const Eᵒᵖ).obj X)).symm).trans
    (HomFamily.evalEquiv e V X)

/-- The index-isomorphism equivalence evaluates at the inverse image of the lifted identity. -/
@[simp, stacks 017M "lifted coyoneda index-isomorphism evaluation formula"]
theorem homEquiv.ofIso.apply {U : E ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftCoyoneda.{w}.obj (op e)) {X : C}
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] {V : Eᵒᵖ ⥤ C}
    (f : V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv.ofIso e a X V f =
      f.app (op e) ≫
        Pi.π (fun _ : U.obj e ↦ X)
          (a.inv.app e (ULift.up (𝟙 e))) := sorry

/-- The inverse index-isomorphism equivalence is assembled degreewise from the transported maps. -/
@[stacks 017M "lifted coyoneda index-isomorphism inverse formula"]
theorem homEquiv.ofIso.symm_apply {U : E ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftCoyoneda.{w}.obj (op e)) (X : C)
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C)
    (f : V.obj (op e) ⟶ X) (Delta : Eᵒᵖ) :
    ((homEquiv.ofIso e a X V).symm f).app Delta =
      Pi.lift (fun u : U.obj (unop Delta) ↦
        V.map (Opposite.op (a.hom.app (unop Delta) u).down) ≫ f) := sorry

/-- Projecting the inverse index-isomorphism equivalence recovers the transported structure map. -/
@[reassoc, stacks 017M "lifted coyoneda inverse projection formula"]
theorem homEquiv.ofIso.symm_apply_π {U : E ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftCoyoneda.{w}.obj (op e)) (X : C)
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C)
    (f : V.obj (op e) ⟶ X) (Delta : Eᵒᵖ)
    (u : U.obj (unop Delta)) :
    ((homEquiv.ofIso e a X V).symm f).app Delta ≫
        Pi.π (fun _ : U.obj (unop Delta) ↦ X) u =
      V.map (Opposite.op (a.hom.app (unop Delta) u).down) ≫ f := sorry

/-- The index-isomorphism equivalence is natural under source precomposition. -/
@[stacks 017M "lifted coyoneda source naturality up to index isomorphism"]
theorem homEquiv.ofIso.precomp {U : E ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftCoyoneda.{w}.obj (op e)) {X : C}
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)]
    {V W : Eᵒᵖ ⥤ C} (g : W ⟶ V)
    (f : V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv.ofIso e a X W (g ≫ f) =
      g.app (op e) ≫ homEquiv.ofIso e a X V f := sorry

/-- The index-isomorphism equivalence is natural under postcomposition in the constant factor. -/
@[stacks 017M "lifted coyoneda constant-object naturality up to index isomorphism"]
theorem homEquiv.ofIso.postcomp {U : E ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftCoyoneda.{w}.obj (op e))
    {X Y : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)]
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (g : V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv.ofIso e a Y V
        (g ≫ indexedProd.hom U ((Functor.const Eᵒᵖ).map f)) =
      homEquiv.ofIso e a X V g ≫ f := sorry

/-- The lifted coyoneda product equivalence evaluates at the lifted identity factor. -/
@[stacks 017M "lifted coyoneda Hom equivalence evaluation formula"]
theorem homEquiv.apply {X : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    (f : V ⟶ indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv e X V f =
      f.app (op e) ≫
        Pi.π (fun _ : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj e ↦ X)
          (ULift.up (𝟙 e)) := sorry

/-- The inverse lifted coyoneda product equivalence is assembled degreewise from structure maps. -/
@[stacks 017M "lifted coyoneda Hom equivalence inverse formula"]
theorem homEquiv.symm_apply {X : C} (V : Eᵒᵖ ⥤ C)
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    (f : V.obj (op e) ⟶ X) (Delta : Eᵒᵖ) :
    ((homEquiv e X V).symm f).app Delta =
      Pi.lift (fun g : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta) ↦
        V.map (Opposite.op g.down) ≫ f) := sorry

/-- Projecting the inverse lifted coyoneda equivalence recovers the structure map followed by `f`. -/
@[reassoc, stacks 017M "lifted coyoneda inverse projection formula"]
theorem homEquiv.symm_apply_π {X : C} (V : Eᵒᵖ ⥤ C)
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    (f : V.obj (op e) ⟶ X) (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta)) :
    ((homEquiv e X V).symm f).app Delta ≫
        Pi.π (fun _ : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta) ↦ X) g =
      V.map (Opposite.op g.down) ≫ f := sorry

/-- The lifted coyoneda product equivalence is natural under source precomposition. -/
@[stacks 017M "lifted coyoneda source naturality"]
theorem homEquiv.precomp {X : C} {V W : Eᵒᵖ ⥤ C}
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    (a : W ⟶ V)
    (f : V ⟶ indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv e X W (a ≫ f) = a.app (op e) ≫ homEquiv e X V f := sorry

/-- The lifted coyoneda product equivalence is natural under postcomposition in the constant
factor. -/
@[stacks 017M "lifted coyoneda constant-object naturality"]
theorem homEquiv.postcomp {X Y : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (g : V ⟶ indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv e Y V
        (g ≫ indexedProd.hom (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
          ((Functor.const Eᵒᵖ).map f)) =
      homEquiv e X V g ≫ f := sorry

/-- The universe-lifted coyoneda product equivalence is natural by precomposition. This is the
coherence field for the canonical representation. -/
@[stacks 017M "lifted coyoneda-indexed product naturality"]
theorem homEquiv.ulift_comp {X : C}
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    {V W : Eᵒᵖ ⥤ C} (a : V ⟶ W)
    (f : W ⟶ indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)) :
    ((homEquiv e X V).trans Equiv.ulift.symm) (a ≫ f) =
      (((((evaluation Eᵒᵖ C).obj (op e)).op ⋙ yoneda.obj X) ⋙
          CategoryTheory.uliftFunctor.{i, v}).map a.op)
        (((homEquiv e X W).trans Equiv.ulift.symm) f) := sorry

/-- The lifted coyoneda-indexed product represents the universe-lifted presheaf of maps from
evaluation at `op e` to `X`. Only the product forming this representing object is required. -/
@[stacks 017M "representability of lifted coyoneda-indexed products"]
def representableBy (X : C)
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)] :
    (((((evaluation Eᵒᵖ C).obj (op e)).op ⋙ yoneda.obj X) ⋙
        CategoryTheory.uliftFunctor.{i, v}).RepresentableBy
      (indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
        ((Functor.const Eᵒᵖ).obj X))) where
  homEquiv {V} := (homEquiv e X V).trans Equiv.ulift.symm
  homEquiv_comp := homEquiv.ulift_comp e (X := X)

/-- The represented Hom equivalence evaluates at the product factor indexed by the lifted
identity of `e`. -/
@[simp, stacks 017M "represented lifted coyoneda Hom equivalence formula"]
theorem representableBy.homEquiv.apply {X : C}
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    {V : Eᵒᵖ ⥤ C}
    (f : V ⟶ indexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)) :
    ((representableBy e X).homEquiv f).down =
      f.app (op e) ≫
        Pi.π (fun _ : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj e ↦ X)
          (ULift.up (𝟙 e)) := sorry

/-- Projecting the inverse represented Hom equivalence recovers the source structure map
followed by the selected map at `op e`. -/
@[reassoc, stacks 017M "represented lifted coyoneda inverse projection formula"]
theorem representableBy.homEquiv.symm_apply_π {X : C}
    [HasIndexedProd (CategoryTheory.uliftCoyoneda.{w}.obj (op e))
      ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) (f : V.obj (op e) ⟶ X) (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta)) :
    ((representableBy e X).homEquiv.symm (ULift.up f)).app Delta ≫
        Pi.π
          (fun _ : (CategoryTheory.uliftCoyoneda.{w}.obj (op e)).obj (unop Delta) ↦ X) g =
      V.map (Opposite.op g.down) ≫ f := sorry

end indexedProd.uliftCoyoneda

end CategoryTheory.Functor
