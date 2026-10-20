/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedProduct.ConstHom
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Coyoneda-indexed products and evaluation

For a representable covariant `Type`-valued functor, the indexed product presheaf is the
right adjoint to evaluation at the representing object.  This module owns the explicit
reindexing maps and the resulting comparison, independently of any simplicial application.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe i w d v u

namespace CategoryTheory.Coyoneda

variable {E : Type i} [Category.{d} E]

/-- In a category with finite Hom-types, every value of a covariant representable functor is
finite. -/
@[stacks 017M "finite covariant representable values"]
instance objFinite [∀ a b : E, Finite (a ⟶ b)] (d : E) :
    (coyoneda.obj (Opposite.op d)).ObjFinite :=
  ⟨fun X ↦ inferInstanceAs (Finite (d ⟶ X))⟩

/-- In a category with nonempty Hom-types, every value of a covariant representable functor is
nonempty. -/
@[stacks 017M "nonempty covariant representable values"]
instance objNonempty [∀ a b : E, Nonempty (a ⟶ b)] (d : E) :
    (coyoneda.obj (op d)).ObjNonempty :=
  ⟨fun X ↦ inferInstanceAs (Nonempty (d ⟶ X))⟩

end CategoryTheory.Coyoneda

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]
variable {E : Type i} [Category.{d} E]
variable (d : E)

namespace indexedProd

namespace coyoneda

section EvaluationComparison

/- The Mathlib evaluation-right-adjoint comparison is deliberately kept in a section with its
   stronger all-target product hypothesis.  The Hom equivalence below only needs one fixed
   representable index and therefore has a smaller interface. -/
variable [∀ a b : Eᵒᵖ, HasProductsOfShape (a ⟶ b) C]

/-- The forward degreewise comparison from the coyoneda-indexed product to the evaluation
right adjoint. -/
@[stacks 017M "coyoneda indexed-product forward component"]
noncomputable def component.hom
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] (Δ : Eᵒᵖ) :
    (indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ ⟶
      ((evaluationRightAdjoint C (Opposite.op d)).obj X).obj Δ :=
  Pi.lift (fun g : Δ ⟶ Opposite.op d ↦
    Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (Opposite.op d)) g))

/-- The inverse degreewise comparison from the evaluation right adjoint to the
coyoneda-indexed product. -/
@[stacks 017M "coyoneda indexed-product inverse component"]
noncomputable def component.inv
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] (Δ : Eᵒᵖ) :
    ((evaluationRightAdjoint C (Opposite.op d)).obj X).obj Δ ⟶
      (indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ :=
  Pi.lift (fun g : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦
    Pi.π (fun _ : Δ ⟶ Opposite.op d ↦ X) ((opEquiv Δ (Opposite.op d)).symm g))

/-- The forward coyoneda component followed by its inverse is the identity. -/
@[stacks 017M "coyoneda indexed-product component inverse law"]
theorem component.hom_inv_id
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] (Δ : Eᵒᵖ) :
    component.hom d X Δ ≫ component.inv d X Δ =
      𝟙 ((indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ) := sorry

/-- The inverse coyoneda component followed by the forward component is the identity. -/
@[stacks 017M "coyoneda indexed-product inverse component law"]
theorem component.inv_hom_id
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] (Δ : Eᵒᵖ) :
    component.inv d X Δ ≫ component.hom d X Δ =
      𝟙 (((evaluationRightAdjoint C (Opposite.op d)).obj X).obj Δ) := sorry

/-- The componentwise comparison from the indexed product over the covariant representable at
`d` to the evaluation right adjoint at `Opposite.op d`.  Its maps explicitly reindex factors through
`opEquiv`; only the inverse laws are deferred in the statement stage. -/
@[stacks 017M "coyoneda indexed-product evaluation component"]
noncomputable def component
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] (Δ : Eᵒᵖ) :
    (indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)).obj Δ ≅
      ((evaluationRightAdjoint C (Opposite.op d)).obj X).obj Δ where
  hom := component.hom d X Δ
  inv := component.inv d X Δ
  hom_inv_id := component.hom_inv_id d X Δ
  inv_hom_id := component.inv_hom_id d X Δ

/-- The forward component of `component` sends the factor indexed
by `g : Δ ⟶ Opposite.op d` to the factor indexed by its covariant-yoneda image. -/
@[stacks 017M "coyoneda component projection formula"]
theorem component.hom_π
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (Δ : Eᵒᵖ) (g : Δ ⟶ Opposite.op d) :
    (component d X Δ).hom ≫
        Pi.π (fun _ : Δ ⟶ Opposite.op d ↦ X) g =
      Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (Opposite.op d)) g) := sorry

/-- The inverse component of `component` sends the factor indexed
by a covariant-yoneda element to the corresponding arrow into `Opposite.op d`. -/
@[stacks 017M "coyoneda inverse projection formula"]
theorem component.inv_π
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (Δ : Eᵒᵖ) (g : (coyoneda.obj (Opposite.op d)).obj (unop Δ)) :
    (component d X Δ).inv ≫
        Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦ X) g =
      Pi.π (fun _ : Δ ⟶ Opposite.op d ↦ X) ((opEquiv Δ (Opposite.op d)).symm g) := sorry

/-- The forward coyoneda component is natural in the presheaf degree. -/
@[stacks 017M "coyoneda indexed-product component naturality"]
theorem component.naturality
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    {Δ Δ' : Eᵒᵖ} (f : Δ ⟶ Δ') :
    (indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)).map f ≫
        (component d X Δ').hom =
      (component d X Δ).hom ≫ ((evaluationRightAdjoint C (Opposite.op d)).obj X).map f := sorry

/-- The indexed product over the covariant representable at `d` is canonically the evaluation
right adjoint at `Opposite.op d`.  The components retain the explicit reindexing data supplied by
`component`. -/
@[stacks 017M "coyoneda indexed-product evaluation comparison"]
noncomputable def iso (X : C)
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] :
    indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X) ≅
      (evaluationRightAdjoint C (Opposite.op d)).obj X :=
  NatIso.ofComponents (component d X) (component.naturality d X)

/-- At `Δ`, the forward map of `iso` has the explicit
factor-reindexing formula induced by `opEquiv Δ (Opposite.op d)`. -/
@[stacks 017M "coyoneda comparison projection formula"]
theorem iso.hom_app_π
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (Δ : Eᵒᵖ) (g : Δ ⟶ Opposite.op d) :
    (iso d X).hom.app Δ ≫
        Pi.π (fun _ : Δ ⟶ Opposite.op d ↦ X) g =
      Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦ X) ((opEquiv Δ (Opposite.op d)) g) := sorry

/-- At `Δ`, the inverse map of `iso` has the complementary projection formula. -/
@[stacks 017M "coyoneda comparison inverse projection formula"]
theorem iso.inv_app_π
    (X : C) [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (Δ : Eᵒᵖ) (g : (coyoneda.obj (Opposite.op d)).obj (unop Δ)) :
    (iso d X).inv.app Δ ≫
        Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦ X) g =
      Pi.π (fun _ : Δ ⟶ Opposite.op d ↦ X)
        ((opEquiv Δ (Opposite.op d)).symm g) := sorry

end EvaluationComparison

namespace HomFamily

/-- Evaluate a compatible family indexed by `coyoneda.obj (Opposite.op d)` at the identity of
`d`. -/
@[stacks 017M "identity evaluation of a coyoneda-indexed Hom family"]
def eval {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedProd.HomFamily.Compatible
      (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X)) :
    V.obj (Opposite.op d) ⟶ X :=
  F.1 (Opposite.op d) (𝟙 d)

/-- Identity evaluation is the identity-indexed component of the compatible family. -/
@[simp, stacks 017M "coyoneda Hom-family identity-evaluation formula"]
theorem eval.apply {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedProd.HomFamily.Compatible
      (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X)) :
    eval d F = F.1 (Opposite.op d) (𝟙 d) := sorry

/-- A map out of `V.obj (Opposite.op d)` induces the coyoneda-indexed family obtained by
precomposing with the structure maps of `V`. -/
@[stacks 017M "Hom family induced by a map at the representing object"]
def ofMap (V : Eᵒᵖ ⥤ C) {X : C} (f : V.obj (Opposite.op d) ⟶ X) :
    indexedProd.HomFamily
      (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X) :=
  fun _ g ↦ V.map (Opposite.op g) ≫ f

/-- Evaluate the coyoneda-indexed family induced by a representing-object map. -/
@[simp, stacks 017M "induced coyoneda Hom-family component"]
theorem ofMap.apply (V : Eᵒᵖ ⥤ C) {X : C} (f : V.obj (Opposite.op d) ⟶ X)
    (Delta : Eᵒᵖ) (g : (coyoneda.obj (Opposite.op d)).obj (unop Delta)) :
    ofMap d V f Delta g = V.map (Opposite.op g) ≫ f := sorry

/-- The family induced by a map at the representing object is compatible. -/
@[stacks 017M "compatibility of an induced coyoneda Hom family"]
theorem ofMap.isCompatible (V : Eᵒᵖ ⥤ C) {X : C}
    (f : V.obj (Opposite.op d) ⟶ X) :
    (ofMap d V f).IsCompatible := sorry

/-- Package the family induced by a representing-object map with its compatibility. -/
@[stacks 017M "compatible family induced at the representing object"]
def ofMap.compatible (V : Eᵒᵖ ⥤ C) {X : C}
    (f : V.obj (Opposite.op d) ⟶ X) :
    indexedProd.HomFamily.Compatible
      (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X) :=
  ⟨ofMap d V f, ofMap.isCompatible d V f⟩

/-- Evaluate a packaged induced family in one degree and at one index. -/
@[simp, stacks 017M "compatible induced coyoneda Hom-family component"]
theorem ofMap.compatible.apply (V : Eᵒᵖ ⥤ C) {X : C}
    (f : V.obj (Opposite.op d) ⟶ X) (Delta : Eᵒᵖ)
    (g : (coyoneda.obj (Opposite.op d)).obj (unop Delta)) :
    (ofMap.compatible d V f).1 Delta g = V.map (Opposite.op g) ≫ f := sorry

/-- Reconstructing a compatible coyoneda-indexed family from its identity value returns the
original family. -/
@[stacks 017M "coyoneda Hom-family reconstruction law"]
theorem ofMap.compatible_eval {X : C} (V : Eᵒᵖ ⥤ C)
    (F : indexedProd.HomFamily.Compatible
      (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X)) :
    ofMap.compatible d V (eval d F) = F := sorry

/-- Evaluating the family induced by a representing-object map returns that map. -/
@[stacks 017M "coyoneda Hom-family evaluation law"]
theorem eval_ofMap {X : C} (V : Eᵒᵖ ⥤ C)
    (f : V.obj (Opposite.op d) ⟶ X) :
    eval d (ofMap.compatible d V f) = f := sorry

/-- Compatible families indexed by `coyoneda.obj (Opposite.op d)` are canonically maps out of
the value at `Opposite.op d`. -/
@[stacks 017M "coyoneda Hom-family evaluation equivalence"]
def evalEquiv (V : Eᵒᵖ ⥤ C) (X : C) :
    indexedProd.HomFamily.Compatible
        (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X) ≃
      (V.obj (Opposite.op d) ⟶ X) where
  toFun := eval d
  invFun := ofMap.compatible d V
  left_inv := ofMap.compatible_eval d V
  right_inv := eval_ofMap d V

/-- The forward map of `evalEquiv` is identity evaluation. -/
@[simp, stacks 017M "coyoneda Hom-family equivalence forward formula"]
theorem evalEquiv.apply {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedProd.HomFamily.Compatible
      (coyoneda.obj (Opposite.op d)) V ((Functor.const Eᵒᵖ).obj X)) :
    evalEquiv d V X F = eval d F := sorry

/-- The inverse of `evalEquiv` is the family induced by the chosen map. -/
@[simp, stacks 017M "coyoneda Hom-family equivalence inverse formula"]
theorem evalEquiv.symm_apply {X : C} (V : Eᵒᵖ ⥤ C)
    (f : V.obj (Opposite.op d) ⟶ X) :
    (evalEquiv d V X).symm f = ofMap.compatible d V f := sorry

end HomFamily

/-- For a covariant representable indexing functor, morphisms into the corresponding indexed
product are canonically morphisms from the value at the representing object.  This direct
construction specializes the generic constant-target indexed-product equivalence and then applies
Mathlib's universe-lifted Coyoneda equivalence.  It keeps the index and target Hom universes
independent and only asks for products indexed by the fixed representable
`coyoneda.obj (Opposite.op d)`.
-/
@[stacks 017M "coyoneda-indexed product Hom equivalence"]
noncomputable def homEquiv (X : C)
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) :
    (V ⟶ indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)) ≃
      (V.obj (Opposite.op d) ⟶ X) :=
  (indexedProd.constHom.uliftEquiv (coyoneda.obj (Opposite.op d)) V X).trans
    (CategoryTheory.uliftCoyonedaEquiv.{v}.trans Equiv.ulift)

/-- If an indexing functor is isomorphic to the covariant representable at `d`, maps into its
indexed product are canonically maps from the value at `d`.  Only the indexed product for the
chosen indexing functor is required. -/
@[stacks 017M "coyoneda-indexed product Hom equivalence up to index isomorphism"]
noncomputable def homEquiv.ofIso {U : E ⥤ Type d}
    (a : U ≅ coyoneda.obj (Opposite.op d)) (X : C)
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C) :
    (V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) ≃
      (V.obj (Opposite.op d) ⟶ X) :=
  ((indexedProd.HomFamily.homEquiv U V ((Functor.const Eᵒᵖ).obj X)).trans
      (indexedProd.HomFamily.restrictEquiv a
        V ((Functor.const Eᵒᵖ).obj X)).symm).trans
    (HomFamily.evalEquiv d V X)

/-- The index-isomorphism coyoneda equivalence evaluates at `d` and projects to the factor
corresponding to the inverse image of the identity morphism. -/
@[simp, stacks 017M "coyoneda index-isomorphism evaluation formula"]
theorem homEquiv.ofIso.apply {U : E ⥤ Type d}
    (a : U ≅ coyoneda.obj (Opposite.op d)) {X : C}
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] {V : Eᵒᵖ ⥤ C}
    (f : V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv.ofIso d a X V f =
      f.app (Opposite.op d) ≫
        Pi.π (fun _ : U.obj d ↦ X)
          (a.inv.app d (𝟙 d)) := sorry

/-- The inverse index-isomorphism coyoneda equivalence is assembled degreewise by transporting
each index through the forward component of the index isomorphism. -/
@[stacks 017M "coyoneda index-isomorphism inverse formula"]
theorem homEquiv.ofIso.symm_apply {U : E ⥤ Type d}
    (a : U ≅ coyoneda.obj (Opposite.op d)) (X : C)
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C)
    (f : V.obj (Opposite.op d) ⟶ X) (Delta : Eᵒᵖ) :
    ((homEquiv.ofIso d a X V).symm f).app Delta =
      Pi.lift (fun u : U.obj (unop Delta) ↦
        V.map (Opposite.op (a.hom.app (unop Delta) u)) ≫ f) := sorry

/-- Projecting the inverse index-isomorphism coyoneda equivalence to one factor gives the
corresponding structure map of `V`, followed by the selected map at `d`. -/
@[reassoc, stacks 017M "coyoneda index-isomorphism inverse projection formula"]
theorem homEquiv.ofIso.symm_apply_π {U : E ⥤ Type d}
    (a : U ≅ coyoneda.obj (Opposite.op d)) (X : C)
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)] (V : Eᵒᵖ ⥤ C)
    (f : V.obj (Opposite.op d) ⟶ X) (Delta : Eᵒᵖ)
    (u : U.obj (unop Delta)) :
    ((homEquiv.ofIso d a X V).symm f).app Delta ≫
        Pi.π (fun _ : U.obj (unop Delta) ↦ X) u =
      V.map (Opposite.op (a.hom.app (unop Delta) u)) ≫ f := sorry

/-- The index-isomorphism coyoneda equivalence is natural under source precomposition. -/
@[stacks 017M "coyoneda index-isomorphism source naturality"]
theorem homEquiv.ofIso.precomp {U : E ⥤ Type d}
    (a : U ≅ coyoneda.obj (Opposite.op d)) {X : C}
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)]
    {V W : Eᵒᵖ ⥤ C} (g : W ⟶ V)
    (f : V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv.ofIso d a X W (g ≫ f) =
      g.app (Opposite.op d) ≫ homEquiv.ofIso d a X V f := sorry

/-- The index-isomorphism coyoneda equivalence is natural under postcomposition in the constant
factor. -/
@[stacks 017M "coyoneda index-isomorphism constant-object naturality"]
theorem homEquiv.ofIso.postcomp {U : E ⥤ Type d}
    (a : U ≅ coyoneda.obj (Opposite.op d))
    {X Y : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj X)]
    [HasIndexedProd U ((Functor.const Eᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (g : V ⟶ indexedProd U ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv.ofIso d a Y V
        (g ≫ indexedProd.hom U ((Functor.const Eᵒᵖ).map f)) =
      homEquiv.ofIso d a X V g ≫ f := sorry

/-- The coyoneda-indexed product Hom equivalence evaluates at the representing object and then
projects to the factor indexed by its identity morphism. -/
@[stacks 017M "coyoneda Hom equivalence evaluation formula"]
theorem homEquiv.apply {X : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (γ : V ⟶ indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv d X V γ =
      γ.app (Opposite.op d) ≫
        Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj d ↦ X) (𝟙 d) := sorry

/-- The inverse coyoneda-indexed product equivalence is assembled degreewise from the maps
`V.map (Opposite.op g) ≫ f`. -/
@[stacks 017M "coyoneda Hom equivalence inverse formula"]
theorem homEquiv.symm_apply {X : C} (V : Eᵒᵖ ⥤ C)
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (f : V.obj (Opposite.op d) ⟶ X) (Δ : Eᵒᵖ) :
    ((homEquiv d X V).symm f).app Δ =
      Pi.lift (fun g : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦
        V.map (Opposite.op g) ≫ f) := sorry

/-- Projecting the inverse coyoneda-indexed product equivalence to the factor indexed by `g`
recovers the corresponding structure map of `V`, followed by `f`. -/
@[reassoc, stacks 017M "coyoneda Hom equivalence inverse projection formula"]
theorem homEquiv.symm_apply_π {X : C} (V : Eᵒᵖ ⥤ C)
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (f : V.obj (Opposite.op d) ⟶ X) (Δ : Eᵒᵖ)
    (g : (coyoneda.obj (Opposite.op d)).obj (unop Δ)) :
    ((homEquiv d X V).symm f).app Δ ≫
        Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Δ) ↦ X) g =
      V.map (Opposite.op g) ≫ f := sorry

/-- The coyoneda-indexed product Hom equivalence is natural by precomposition in its source
presheaf. -/
@[stacks 017M "coyoneda Hom equivalence source naturality"]
theorem homEquiv.precomp {X : C} {V W : Eᵒᵖ ⥤ C}
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (a : W ⟶ V)
    (γ : V ⟶ indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv d X W (a ≫ γ) = a.app (Opposite.op d) ≫ homEquiv d X V γ := sorry

/-- The coyoneda-indexed product Hom equivalence is natural by postcomposition in the target
object. -/
@[stacks 017M "coyoneda Hom equivalence target naturality"]
theorem homEquiv.postcomp {X Y : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (γ : V ⟶ indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)) :
    homEquiv d Y V
        (γ ≫ CategoryTheory.Functor.indexedProd.hom
          (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).map f)) =
      homEquiv d X V γ ≫ f := sorry

/-- The lifted coyoneda Hom equivalence is natural by precomposition in the source presheaf.
This is the coherence field used by the canonical representation below. -/
@[stacks 017M "lifted coyoneda Hom equivalence naturality"]
theorem homEquiv.ulift_comp {X : C}
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    {V W : Eᵒᵖ ⥤ C} (a : V ⟶ W)
    (γ : W ⟶ indexedProd (coyoneda.obj (Opposite.op d))
      ((Functor.const Eᵒᵖ).obj X)) :
    ((homEquiv d X V).trans Equiv.ulift.symm) (a ≫ γ) =
      (((((evaluation Eᵒᵖ C).obj (Opposite.op d)).op ⋙ yoneda.obj X) ⋙
          CategoryTheory.uliftFunctor.{i, v}).map a.op)
        (((homEquiv d X W).trans Equiv.ulift.symm) γ) := sorry

/-- The coyoneda-indexed product represents the universe-lifted presheaf of maps from evaluation
at `d` to `X`.  Unlike the global evaluation adjunction, this fixed-target owner only requires
the products used to form this one representing object. -/
@[stacks 017M "representability of coyoneda-indexed products"]
noncomputable def representableBy (X : C)
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)] :
    (((((evaluation Eᵒᵖ C).obj (Opposite.op d)).op ⋙ yoneda.obj X) ⋙
        CategoryTheory.uliftFunctor.{i, v}).RepresentableBy
      (indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X))) where
  homEquiv {V} := (homEquiv d X V).trans Equiv.ulift.symm
  homEquiv_comp := homEquiv.ulift_comp d (X := X)

/-- The represented Hom equivalence is the original coyoneda equivalence followed by universe
lifting. -/
@[simp, stacks 017M "represented coyoneda Hom equivalence formula"]
theorem representableBy.homEquiv.apply {X : C}
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    {V : Eᵒᵖ ⥤ C}
    (γ : V ⟶ indexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)) :
    ((representableBy d X).homEquiv γ).down =
      γ.app (Opposite.op d) ≫
        Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj d ↦ X) (𝟙 d) := sorry

/-- Projecting the inverse represented Hom equivalence recovers the structure map of the source
presheaf followed by the specified map at `d`. -/
@[reassoc, stacks 017M "represented coyoneda inverse projection formula"]
theorem representableBy.homEquiv.symm_apply_π {X : C}
    [HasIndexedProd (coyoneda.obj (Opposite.op d)) ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) (f : V.obj (Opposite.op d) ⟶ X) (Delta : Eᵒᵖ)
    (g : (coyoneda.obj (Opposite.op d)).obj (unop Delta)) :
    ((representableBy d X).homEquiv.symm (ULift.up f)).app Delta ≫
        Pi.π (fun _ : (coyoneda.obj (Opposite.op d)).obj (unop Delta) ↦ X) g =
      V.map (Opposite.op g) ≫ f := sorry

end coyoneda

end indexedProd

end CategoryTheory.Functor
