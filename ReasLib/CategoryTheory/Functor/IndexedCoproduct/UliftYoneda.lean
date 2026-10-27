/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.IndexedCoproduct.HomFamily
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Yoneda-indexed coproducts and evaluation

An indexed coproduct whose indexing presheaf is a universe-lifted representable is the
category-generic tensor form of the Yoneda lemma.  Maps from that indexed coproduct are
canonically maps from the constant factor into the value of the target presheaf at the
representing object.

This is the coproduct-side owner dual to `Functor.indexedProd.coyoneda`; simplicial copowers
by standard simplices are direct specializations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe w i d v u

namespace CategoryTheory.Functor

variable {E : Type i} [Category.{d} E]
variable {C : Type u} [Category.{v} C]

namespace indexedCoprod.uliftYoneda

variable (e : E)

namespace HomFamily

/-- Evaluate a compatible family indexed by `uliftYoneda.obj e` at the lifted identity of
`e`. -/
@[stacks 017F "identity evaluation of a Yoneda-indexed coproduct family"]
def eval {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedCoprod.HomFamily.Compatible
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V) :
    X ⟶ V.obj (op e) :=
  F.1 (op e) (ULift.up (𝟙 e))

/-- Identity evaluation is the lifted-identity component of the compatible family. -/
@[simp, stacks 017F "Yoneda-indexed family evaluation formula"]
theorem eval.apply {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedCoprod.HomFamily.Compatible
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V) :
    eval e F = F.1 (op e) (ULift.up (𝟙 e)) := rfl

/-- A map from the constant factor into `V.obj (op e)` induces a Yoneda-indexed family by
postcomposing with the structure maps of `V`. -/
@[stacks 017F "family induced by a map at the representing object"]
def ofMap (V : Eᵒᵖ ⥤ C) {X : C} (f : X ⟶ V.obj (op e)) :
    indexedCoprod.HomFamily
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V :=
  fun _ g ↦ f ≫ V.map g.down.op

/-- The component of the family induced by a representing-object map. -/
@[simp, stacks 017F "induced Yoneda-indexed family component"]
theorem ofMap.apply (V : Eᵒᵖ ⥤ C) {X : C} (f : X ⟶ V.obj (op e))
    (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftYoneda.{w}.obj e).obj Delta) :
    ofMap e V f Delta g = f ≫ V.map g.down.op := rfl

/-- The family induced by a map at the representing object is compatible. -/
@[stacks 017F "compatibility of an induced Yoneda-indexed family"]
theorem ofMap.isCompatible (V : Eᵒᵖ ⥤ C) {X : C}
    (f : X ⟶ V.obj (op e)) :
    (ofMap e V f).IsCompatible := by
  intro Delta Delta' h g
  change 𝟙 X ≫ (f ≫ V.map (g.down.op ≫ h)) =
    (f ≫ V.map g.down.op) ≫ V.map h
  rw [Category.id_comp, V.map_comp, Category.assoc]

/-- Package the family induced by a representing-object map with its compatibility. -/
@[stacks 017F "compatible family induced at the representing object"]
def ofMap.compatible (V : Eᵒᵖ ⥤ C) {X : C}
    (f : X ⟶ V.obj (op e)) :
    indexedCoprod.HomFamily.Compatible
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V :=
  ⟨ofMap e V f, ofMap.isCompatible e V f⟩

/-- Evaluate a packaged induced family in one degree and at one index. -/
@[simp, stacks 017F "compatible induced Yoneda-indexed family component"]
theorem ofMap.compatible.apply (V : Eᵒᵖ ⥤ C) {X : C}
    (f : X ⟶ V.obj (op e)) (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftYoneda.{w}.obj e).obj Delta) :
    (ofMap.compatible e V f).1 Delta g = f ≫ V.map g.down.op := rfl

/-- Reconstructing a compatible Yoneda-indexed family from its identity value returns the
original family. -/
@[stacks 017F "Yoneda-indexed family reconstruction law"]
theorem ofMap.compatible_eval {X : C} (V : Eᵒᵖ ⥤ C)
    (F : indexedCoprod.HomFamily.Compatible
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V) :
    ofMap.compatible e V (eval e F) = F := by
  apply Subtype.ext
  funext Delta g
  obtain ⟨g⟩ := g
  change F.1 (op e) (ULift.up (𝟙 e)) ≫ V.map g.op =
    F.1 Delta (ULift.up g)
  have h := (F.2 g.op (ULift.up (𝟙 e))).symm
  change F.1 (op e) (ULift.up (𝟙 e)) ≫ V.map g.op =
    𝟙 X ≫ F.1 Delta (ULift.up (g ≫ 𝟙 e)) at h
  simpa using h

/-- Evaluating the family induced by a representing-object map returns that map. -/
@[stacks 017F "Yoneda-indexed family evaluation law"]
theorem eval_ofMap {X : C} (V : Eᵒᵖ ⥤ C)
    (f : X ⟶ V.obj (op e)) :
    eval e (ofMap.compatible e V f) = f := by
  change f ≫ V.map (𝟙 (op e)) = f
  simp

/-- Compatible families indexed by `uliftYoneda.obj e` are canonically maps from the constant
factor into the value at `op e`. -/
@[stacks 017F "Yoneda-indexed compatible-family evaluation equivalence"]
def evalEquiv (X : C) (V : Eᵒᵖ ⥤ C) :
    indexedCoprod.HomFamily.Compatible
        (CategoryTheory.uliftYoneda.{w}.obj e)
        ((Functor.const Eᵒᵖ).obj X) V ≃
      (X ⟶ V.obj (op e)) where
  toFun := eval e
  invFun := ofMap.compatible e V
  left_inv := ofMap.compatible_eval e V
  right_inv := eval_ofMap e V

/-- The forward map of `evalEquiv` is identity evaluation. -/
@[simp, stacks 017F "Yoneda-indexed family equivalence forward formula"]
theorem evalEquiv.apply {X : C} {V : Eᵒᵖ ⥤ C}
    (F : indexedCoprod.HomFamily.Compatible
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V) :
    evalEquiv e X V F = eval e F := rfl

/-- The inverse of `evalEquiv` is the family induced by the chosen map. -/
@[simp, stacks 017F "Yoneda-indexed family equivalence inverse formula"]
theorem evalEquiv.symm_apply (X : C) (V : Eᵒᵖ ⥤ C)
    (f : X ⟶ V.obj (op e)) :
    (evalEquiv e X V).symm f = ofMap.compatible e V f := rfl

end HomFamily

/-- Maps from the Yoneda-indexed coproduct of a constant diagram are canonically maps from the
constant factor into the target value at the representing object.  Only the one fixed indexed
coproduct occurring in the source is required. -/
@[stacks 017F "Yoneda-indexed coproduct Hom equivalence"]
def homEquiv (X : C)
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) :
    (indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
        ((Functor.const Eᵒᵖ).obj X) ⟶ V) ≃
      (X ⟶ V.obj (op e)) :=
  (indexedCoprod.HomFamily.homEquiv
      (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) V).trans
    (HomFamily.evalEquiv e X V)

/-- If an indexing presheaf is isomorphic to `uliftYoneda.obj e`, maps from its indexed
coproduct are still canonically maps into the target value at `op e`.  This formulation only
requires the indexed coproduct for the given presheaf. -/
@[stacks 017F "Yoneda-indexed coproduct Hom equivalence up to index isomorphism"]
def homEquiv.ofIso {U : Eᵒᵖ ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftYoneda.{w}.obj e) (X : C)
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) :
    (indexedCoprod U ((Functor.const Eᵒᵖ).obj X) ⟶ V) ≃
      (X ⟶ V.obj (op e)) :=
  ((indexedCoprod.HomFamily.homEquiv U ((Functor.const Eᵒᵖ).obj X) V).trans
      (indexedCoprod.HomFamily.restrictEquiv a
        ((Functor.const Eᵒᵖ).obj X) V).symm).trans
    (HomFamily.evalEquiv e X V)

/-- The equivalence for an index presheaf isomorphic to a representable evaluates on the
summand corresponding to the inverse image of the lifted identity. -/
@[stacks 017F "Yoneda-indexed coproduct evaluation up to index isomorphism"]
theorem homEquiv.ofIso.apply {U : Eᵒᵖ ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftYoneda.{w}.obj e) {X : C}
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj X)]
    {V : Eᵒᵖ ⥤ C}
    (f : indexedCoprod U ((Functor.const Eᵒᵖ).obj X) ⟶ V) :
    homEquiv.ofIso e a X V f =
      Sigma.ι (fun _ : U.obj (op e) ↦ X)
          (a.inv.app (op e) (ULift.up (𝟙 e))) ≫
        f.app (op e) := rfl

/-- The inverse equivalence for an index presheaf isomorphic to a representable is assembled
degreewise after sending each index through the forward isomorphism. -/
@[stacks 017F "Yoneda-indexed coproduct inverse up to index isomorphism"]
theorem homEquiv.ofIso.symm_apply {U : Eᵒᵖ ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftYoneda.{w}.obj e) (X : C)
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) (f : X ⟶ V.obj (op e)) (Delta : Eᵒᵖ) :
    ((homEquiv.ofIso e a X V).symm f).app Delta =
      Sigma.desc (fun u : U.obj Delta ↦
        f ≫ V.map ((a.hom.app Delta u).down).op) := rfl

/-- Restricting the inverse equivalence to one summand gives the structure map determined by
the corresponding representable index. -/
@[reassoc, stacks 017F "Yoneda-indexed coproduct inverse injection up to index isomorphism"]
theorem homEquiv.ofIso.symm_apply_ι {U : Eᵒᵖ ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftYoneda.{w}.obj e) (X : C)
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj X)]
    (V : Eᵒᵖ ⥤ C) (f : X ⟶ V.obj (op e))
    (Delta : Eᵒᵖ) (u : U.obj Delta) :
    Sigma.ι (fun _ : U.obj Delta ↦ X) u ≫
        ((homEquiv.ofIso e a X V).symm f).app Delta =
      f ≫ V.map ((a.hom.app Delta u).down).op := by
  rw [homEquiv.ofIso.symm_apply]
  exact Sigma.ι_desc _ u

/-- The equivalence up to index isomorphism is natural under postcomposition in the target
presheaf. -/
@[stacks 017F "Yoneda-indexed coproduct target naturality up to index isomorphism"]
theorem homEquiv.ofIso.postcomp {U : Eᵒᵖ ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftYoneda.{w}.obj e) {X : C}
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj X)]
    {V W : Eᵒᵖ ⥤ C}
    (f : indexedCoprod U ((Functor.const Eᵒᵖ).obj X) ⟶ V)
    (g : V ⟶ W) :
    homEquiv.ofIso e a X W (f ≫ g) =
      homEquiv.ofIso e a X V f ≫ g.app (op e) := by
  rw [homEquiv.ofIso.apply, homEquiv.ofIso.apply]
  exact (Category.assoc _ _ _).symm

/-- The equivalence up to index isomorphism is natural under precomposition in the constant
factor. -/
@[stacks 017F "Yoneda-indexed coproduct source naturality up to index isomorphism"]
theorem homEquiv.ofIso.precomp {U : Eᵒᵖ ⥤ Type (max w d)}
    (a : U ≅ CategoryTheory.uliftYoneda.{w}.obj e)
    {X Y : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj X)]
    [HasIndexedCoprod U ((Functor.const Eᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (g : indexedCoprod U ((Functor.const Eᵒᵖ).obj Y) ⟶ V) :
    homEquiv.ofIso e a X V
        (indexedCoprod.hom U ((Functor.const Eᵒᵖ).map f) ≫ g) =
      f ≫ homEquiv.ofIso e a Y V g := by
  exact congrArg
    (fun F : indexedCoprod.HomFamily.Compatible U
        ((Functor.const Eᵒᵖ).obj X) V ↦
      F.1 (op e) (a.inv.app (op e) (ULift.up (𝟙 e))))
    (indexedCoprod.HomFamily.homEquiv.precompose
      ((Functor.const Eᵒᵖ).map f) g)

/-- The Yoneda-indexed coproduct equivalence evaluates the component at `op e` after the
coproduct injection indexed by the lifted identity of `e`. -/
@[stacks 017F "Yoneda-indexed coproduct evaluation formula"]
theorem homEquiv.apply {X : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    (f : indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) ⟶ V) :
    homEquiv e X V f =
      Sigma.ι (fun _ : (CategoryTheory.uliftYoneda.{w}.obj e).obj (op e) ↦ X)
        (ULift.up (𝟙 e)) ≫ f.app (op e) := rfl

/-- The inverse Yoneda-indexed coproduct equivalence is assembled degreewise from the maps
`f ≫ V.map g.down.op`. -/
@[stacks 017F "Yoneda-indexed coproduct inverse component"]
theorem homEquiv.symm_apply (X : C) (V : Eᵒᵖ ⥤ C)
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    (f : X ⟶ V.obj (op e)) (Delta : Eᵒᵖ) :
    ((homEquiv e X V).symm f).app Delta =
      Sigma.desc (fun g : (CategoryTheory.uliftYoneda.{w}.obj e).obj Delta ↦
        f ≫ V.map g.down.op) := rfl

/-- Restricting the inverse Yoneda-indexed coproduct equivalence to the summand indexed by `g`
recovers `f` followed by the corresponding structure map of the target presheaf. -/
@[reassoc, stacks 017F "Yoneda-indexed coproduct inverse injection formula"]
theorem homEquiv.symm_apply_ι (X : C) (V : Eᵒᵖ ⥤ C)
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    (f : X ⟶ V.obj (op e)) (Delta : Eᵒᵖ)
    (g : (CategoryTheory.uliftYoneda.{w}.obj e).obj Delta) :
    Sigma.ι (fun _ : (CategoryTheory.uliftYoneda.{w}.obj e).obj Delta ↦ X) g ≫
        ((homEquiv e X V).symm f).app Delta =
      f ≫ V.map g.down.op := by
  rw [homEquiv.symm_apply]
  exact Sigma.ι_desc _ g

/-- The Yoneda-indexed coproduct equivalence is natural under postcomposition in the target
presheaf. -/
@[stacks 017F "Yoneda-indexed coproduct target naturality"]
theorem homEquiv.postcomp {X : C} {V W : Eᵒᵖ ⥤ C}
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    (f : indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) ⟶ V)
    (g : V ⟶ W) :
    homEquiv e X W (f ≫ g) =
      homEquiv e X V f ≫ g.app (op e) := by
  rw [homEquiv.apply, homEquiv.apply]
  exact (Category.assoc _ _ _).symm

/-- The Yoneda-indexed coproduct equivalence is natural under precomposition in the constant
factor. -/
@[stacks 017F "Yoneda-indexed coproduct source naturality"]
theorem homEquiv.precomp {X Y : C} {V : Eᵒᵖ ⥤ C}
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj Y)]
    (f : X ⟶ Y)
    (g : indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj Y) ⟶ V) :
    homEquiv e X V
        (indexedCoprod.hom (CategoryTheory.uliftYoneda.{w}.obj e)
          ((Functor.const Eᵒᵖ).map f) ≫ g) =
      f ≫ homEquiv e Y V g := by
  exact congrArg (HomFamily.eval e)
    (indexedCoprod.HomFamily.homEquiv.precompose
      ((Functor.const Eᵒᵖ).map f) g)

/-- The universe-lifted Yoneda-indexed Hom equivalence is natural by postcomposition.  This is
the coherence field for the canonical corepresentation. -/
@[stacks 017F "lifted Yoneda-indexed coproduct naturality"]
theorem homEquiv.ulift_comp {X : C}
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    {V W : Eᵒᵖ ⥤ C} (g : V ⟶ W)
    (f : indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) ⟶ V) :
    ((homEquiv e X W).trans Equiv.ulift.symm) (f ≫ g) =
      ((((evaluation Eᵒᵖ C).obj (op e) ⋙ coyoneda.obj (op X)) ⋙
          CategoryTheory.uliftFunctor.{i, v}).map g)
        (((homEquiv e X V).trans Equiv.ulift.symm) f) := by
  change ULift.up (homEquiv e X W (f ≫ g)) =
    ULift.up (homEquiv e X V f ≫ g.app (op e))
  exact congrArg ULift.up (homEquiv.postcomp e f g)

/-- The Yoneda-indexed coproduct corepresents the universe-lifted functor of maps from the
constant factor into evaluation at the representing object. -/
@[stacks 017F "corepresentability of Yoneda-indexed coproducts"]
def corepresentableBy (X : C)
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)] :
    (((evaluation Eᵒᵖ C).obj (op e) ⋙ coyoneda.obj (op X)) ⋙
        CategoryTheory.uliftFunctor.{i, v}).CorepresentableBy
      (indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
        ((Functor.const Eᵒᵖ).obj X)) where
  homEquiv {V} := (homEquiv e X V).trans Equiv.ulift.symm
  homEquiv_comp := homEquiv.ulift_comp e

/-- The represented Hom equivalence is the Yoneda-indexed coproduct equivalence followed by
universe lifting. -/
@[simp, stacks 017F "corepresented Yoneda-indexed coproduct formula"]
theorem corepresentableBy.homEquiv.apply {X : C}
    [HasIndexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X)]
    {V : Eᵒᵖ ⥤ C}
    (f : indexedCoprod (CategoryTheory.uliftYoneda.{w}.obj e)
      ((Functor.const Eᵒᵖ).obj X) ⟶ V) :
    (corepresentableBy e X).homEquiv f =
      ULift.up (homEquiv e X V f) := rfl

end indexedCoprod.uliftYoneda

end CategoryTheory.Functor
