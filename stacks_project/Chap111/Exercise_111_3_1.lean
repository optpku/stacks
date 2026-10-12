/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Field.Defs
public import ReasLib.CategoryTheory.Filtration.Preabelian
public import ReasLib.CategoryTheory.Filtration.Strict.Abelian.Basic
public import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace CategoryTheory

section
variable {k : Type u} [Field k]
variable {V W : FilteredObject (ModuleCat.{u} k)} (f : V ⟶ W)

/- Exercise 111.3.1 (1): the category of filtered k-vector spaces is additive. -/
@[stacks 057Y]
#check (inferInstance : Preadditive (FilteredObject (ModuleCat.{u} k)))
@[stacks 057Y]
#check (inferInstance : HasZeroObject (FilteredObject (ModuleCat.{u} k)))
@[stacks 057Y]
#check (inferInstance : HasBinaryBiproducts (FilteredObject (ModuleCat.{u} k)))

/- Exercise 111.3.1 (2): a morphism of filtered k-vector spaces has a kernel given by the
underlying kernel equipped with the induced filtration. -/
@[stacks 057Y]
#check (FilteredObject.Hom.kernel f)
@[stacks 057Y]
#check (FilteredObject.Hom.kernelιIsLimit f)

/- Exercise 111.3.1 (3): a morphism of filtered k-vector spaces has a cokernel given by the
underlying cokernel equipped with the quotient filtration. -/
@[stacks 057Y]
#check (FilteredObject.Hom.cokernel f)
@[stacks 057Y]
#check (FilteredObject.Hom.toCokernelIsColimit f)

end

namespace FilteredObject

/-- The canonical comparison from the underlying object of a binary biproduct of filtered
k-vector spaces to the biproduct of the underlying vector spaces. -/
def biprodObjIso {k : Type u} [Field k] (V W : FilteredObject (ModuleCat.{u} k)) :
    (V ⊞ W).obj ≅ V.obj ⊞ W.obj where
  hom :=
    biprod.lift (biprod.fst : V ⊞ W ⟶ V).hom (biprod.snd : V ⊞ W ⟶ W).hom
  inv :=
    biprod.desc (biprod.inl : V ⟶ V ⊞ W).hom (biprod.inr : W ⟶ V ⊞ W).hom
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying comparison of `biprodObjIso` is the biproduct lift of the underlying first
and second projections. -/
theorem biprodObjIso_hom {k : Type u} [Field k] (V W : FilteredObject (ModuleCat.{u} k)) :
    (biprodObjIso V W).hom =
      biprod.lift (biprod.fst : V ⊞ W ⟶ V).hom (biprod.snd : V ⊞ W ⟶ W).hom := sorry

/-- The canonical stagewise comparison from a binary biproduct of filtered k-vector spaces to
the biproduct of the corresponding stages. -/
def biprodStageIso {k : Type u} [Field k]
    (V W : FilteredObject (ModuleCat.{u} k)) (p : ℤ) :
    (V ⊞ W).stage p ≅ V.stage p ⊞ W.stage p where
  hom :=
    biprod.lift (Hom.stageMap (biprod.fst : V ⊞ W ⟶ V) p)
      (Hom.stageMap (biprod.snd : V ⊞ W ⟶ W) p)
  inv :=
    biprod.desc (Hom.stageMap (biprod.inl : V ⟶ V ⊞ W) p)
      (Hom.stageMap (biprod.inr : W ⟶ V ⊞ W) p)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The stagewise biproduct comparison projects to the first stage map. -/
theorem biprodStageIso_hom_fst {k : Type u} [Field k]
    (V W : FilteredObject (ModuleCat.{u} k)) (p : ℤ) :
    (biprodStageIso V W p).hom ≫ biprod.fst =
      Hom.stageMap (biprod.fst : V ⊞ W ⟶ V) p := sorry

/-- The jump filtration on a k-vector space that is whole in degrees `≤ n` and zero afterwards. -/
def step (k : Type u) [Field k] (n : ℤ) (V : ModuleCat.{u} k) :
    FilteredObject (ModuleCat.{u} k) where
  obj := V
  filtration :=
    { toFun := fun p ↦ if OrderDual.ofDual p ≤ n then ⊤ else ⊥
      monotone' := sorry }

/-- The jump filtration is whole exactly in degrees `≤ n`. -/
theorem step_stage (k : Type u) [Field k] (n : ℤ) (V : ModuleCat.{u} k) (p : ℤ) :
    (step k n V).filtration.stage p = if p ≤ n then ⊤ else ⊥ := sorry

/-- The one-dimensional k-line with jump filtration at `n`. -/
def line (k : Type u) [Field k] (n : ℤ) :
    FilteredObject (ModuleCat.{u} k) :=
  step k n (ModuleCat.of k k)

/-- The underlying object of the jump-filtered line is the one-dimensional space `k`. -/
theorem line_obj (k : Type u) [Field k] (n : ℤ) :
    (line k n).obj = ModuleCat.of k k := sorry

/-- The identity of `k`, viewed as a filtered map from the jump at `-1` to the jump at `0`. -/
def lineId (k : Type u) [Field k] : line k (-1) ⟶ line k 0 where
  hom := 𝟙 (ModuleCat.of k k)
  preserves := sorry

/-- The underlying morphism of `lineId` is the identity of `k`. -/
theorem lineId_hom (k : Type u) [Field k] :
    (lineId k).hom = 𝟙 (ModuleCat.of k k) := sorry

/-- Exercise 111.3.1 (4): the identity of the line with jump filtrations at `-1` and `0` has
filtered coimage-image comparison Hom.coimageImageComparison that is not an isomorphism. -/
@[stacks 057Y]
theorem not_isIso_coimageImageComparison_lineId (k : Type u) [Field k] :
    ¬ IsIso (Hom.coimageImageComparison (lineId k)) := sorry

end FilteredObject

end CategoryTheory

