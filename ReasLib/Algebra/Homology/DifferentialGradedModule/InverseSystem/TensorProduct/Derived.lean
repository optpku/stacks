/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.InverseSystem.HomOver
public import ReasLib.Algebra.Homology.DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Derived.Restriction
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stagewise relative derived tensor towers

For a right object of `D(ℕ, A)` and a left object of the corresponding global derived
category, this file forms the inverse system whose stage `n` is their relative derived tensor
over `A n`.  The transition API is stated for every inequality, so downstream arguments do not
need to unfold the successor presentation of the tower.
-/

@[expose] public section

noncomputable section

universe u x v w

open CategoryTheory Opposite

namespace DifferentialGradedModule.InverseSystem.TensorProduct.Derived

variable {R : Type u} [CommRing R]
variable {A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)}

/-- The stagewise relative derived tensor of a right and a left global derived module system. -/
@[stacks 0GZI "stagewise relative derived tensor over an inverse DGA system"]
noncomputable abbrev stage
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    (n : ℕ) : DerivedCategory (ModuleCat.{max v w} R) :=
  DifferentialGradedModule.TensorProduct.Derived.obj (A.obj (op n))
    ((DifferentialGradedModule.InverseSystem.Derived.eval A n).obj M)
    ((DifferentialGradedModule.InverseSystem.Derived.Left.eval A n).obj N)

/-- A cross-index morphism of left global derived systems induces a cross-index morphism of
their relative derived tensor stages. -/
@[stacks 0GZI "cross-index map of stagewise relative derived tensors"]
noncomputable def mapLeftLE
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    {i j : ℕ} {hij : i ≤ j}
    (g : DifferentialGradedModule.InverseSystem.Derived.Left.HomOver A N N' hij) :
    stage M N j ⟶ stage M N' i :=
  DifferentialGradedModule.TensorProduct.Derived.mapOver (A.transitionMap hij)
    ((DifferentialGradedModule.InverseSystem.Derived.Restriction.comparison A hij).app M)
    g

/-- The relative derived tensor transition from stage `j` to stage `i`, for `i ≤ j`. -/
@[stacks 0GZI "transition of the stagewise relative derived tensor tower"]
noncomputable def mapLE
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {i j : ℕ} (hij : i ≤ j) : stage M N j ⟶ stage M N i :=
  mapLeftLE M
    (DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.transition A N hij)

/-- Tensoring the identity cross-index map gives the identity stage map. -/
@[simp]
theorem mapLeftLE_id
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    (i : ℕ) :
    mapLeftLE M
        (DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.id A N i) =
      𝟙 (stage M N i) := sorry

/-- Tensoring consecutive cross-index left maps agrees with tensoring their composite. -/
theorem mapLeftLE_comp
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {L N P : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    {i j k : ℕ} {hij : i ≤ j} {hjk : j ≤ k}
    (f : DifferentialGradedModule.InverseSystem.Derived.Left.HomOver A L N hjk)
    (g : DifferentialGradedModule.InverseSystem.Derived.Left.HomOver A N P hij) :
    mapLeftLE M f ≫ mapLeftLE M g =
      mapLeftLE M
        (DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.comp f g) := sorry

/-- Tensoring a canonical left-system transition recovers the tensor-tower transition. -/
@[simp]
theorem mapLeftLE_transition
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {i j : ℕ} (hij : i ≤ j) :
    mapLeftLE M
        (DifferentialGradedModule.InverseSystem.Derived.Left.HomOver.transition A N hij) =
      mapLE M N hij := sorry

/-- The tensor transition over a reflexive inequality is the identity. -/
@[simp]
theorem mapLE_refl
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    (i : ℕ) : mapLE M N (le_refl i) = 𝟙 (stage M N i) := sorry

/-- Relative derived tensor transitions compose through every intermediate index. -/
theorem mapLE_comp
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    mapLE M N (Nat.le_trans hij hjk) = mapLE M N hjk ≫ mapLE M N hij := sorry

/-- The adjacent transition of the stagewise relative derived tensor tower. -/
noncomputable abbrev step
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    (n : ℕ) : stage M N (n + 1) ⟶ stage M N n :=
  mapLE M N (Nat.le_add_right n 1)

/-- The inverse system of stagewise relative derived tensors of two global derived module
systems. -/
@[stacks 0GZI "stagewise relative derived tensor tower"]
noncomputable def tower
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) :=
  Functor.ofOpSequence (X := fun n ↦ stage M N n) (step M N)

/-- Evaluation of the stagewise relative derived tensor tower. -/
@[simp]
theorem tower_obj
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    (n : ℕ) : (tower M N).obj (op n) = stage M N n := sorry

/-- The successor map of the tensor tower is its adjacent tensor transition. -/
@[simp]
theorem tower_stepMap
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    (n : ℕ) : (tower M N).stepMap n = step M N n := sorry

/-- Every transition of the tensor tower is the canonical map induced over the corresponding
DGA transition. -/
@[stacks 0GZI "arbitrary transition in a relative derived tensor tower"]
theorem tower_transitionMap
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {i j : ℕ} (hij : i ≤ j) :
    (tower M N).transitionMap hij = mapLE M N hij := sorry

namespace RepresentedLeft

/-- The source-shaped stagewise relative derived tensor attached to an ordinary left DG-module
system. -/
@[stacks 0GZI "stagewise relative derived tensor for an ordinary left module system"]
noncomputable abbrev stage
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    (n : ℕ) : DerivedCategory (ModuleCat.{max v w} R) :=
  DifferentialGradedModule.TensorProduct.Derived.obj (A.obj (op n))
    ((DifferentialGradedModule.InverseSystem.Derived.eval A n).obj M)
    ((DifferentialGradedModule.InverseSystem.Derived.Left.stageSource A n).obj N)

/-- Derived stage evaluation identifies the canonical global tensor stage with the stagewise
tensor of the original left DG-module system. -/
@[stacks 0GZI "comparison with the represented stagewise relative derived tensor"]
noncomputable def stageIso
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    (n : ℕ) :
    DifferentialGradedModule.InverseSystem.TensorProduct.Derived.stage M
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N) n ≅
      stage M N n :=
  ((DifferentialGradedModule.TensorProduct.Derived.functor (A.obj (op n))).obj
    ((DifferentialGradedModule.InverseSystem.Derived.eval A n).obj M)).mapIso
      ((DifferentialGradedModule.InverseSystem.Derived.Left.evalFactors A n).app N)

/-- A derived cross-index morphism of ordinary left systems induces a cross-index morphism of
their represented relative derived tensor stages. -/
@[stacks 0GZI "cross-index map of represented relative derived tensors"]
noncomputable def mapLeftLE
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A}
    {i j : ℕ} {hij : i ≤ j}
    (g : DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver
      A N N' hij) : stage M N j ⟶ stage M N' i :=
  DifferentialGradedModule.TensorProduct.Derived.mapOver (A.transitionMap hij)
    ((DifferentialGradedModule.InverseSystem.Derived.Restriction.comparison A hij).app M)
    g

/-- The tensor transition attached to an ordinary left DG-module system. -/
@[stacks 0GZI "transition of a represented relative derived tensor tower"]
noncomputable def mapLE
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    {i j : ℕ} (hij : i ≤ j) : stage M N j ⟶ stage M N i :=
  mapLeftLE M
    (DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver.transition
      A N hij)

/-- Tensoring the identity derived cross-index map gives the identity represented stage map. -/
@[simp]
theorem mapLeftLE_id
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    (i : ℕ) :
    mapLeftLE M
        (DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver.id A N i) =
      𝟙 (stage M N i) := sorry

/-- Tensoring consecutive derived cross-index maps of ordinary left systems agrees with
tensoring their composite. -/
theorem mapLeftLE_comp
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {L N P : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A}
    {i j k : ℕ} {hij : i ≤ j} {hjk : j ≤ k}
    (f : DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver A L N hjk)
    (g : DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver A N P hij) :
    mapLeftLE M f ≫ mapLeftLE M g =
      mapLeftLE M
        (DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver.comp f g) := sorry

/-- Tensoring the canonical derived transition of an ordinary left system recovers the
represented tensor-tower transition. -/
@[simp]
theorem mapLeftLE_transition
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    {i j : ℕ} (hij : i ≤ j) :
    mapLeftLE M
        (DifferentialGradedModule.InverseSystem.LeftSystem.Derived.HomOver.transition
          A N hij) = mapLE M N hij := sorry

/-- The represented tensor transition over a reflexive inequality is the identity. -/
@[simp]
theorem mapLE_refl
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    (i : ℕ) : mapLE M N (le_refl i) = 𝟙 (stage M N i) := sorry

/-- Represented relative derived tensor transitions compose through every intermediate
index. -/
theorem mapLE_comp
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    mapLE M N (Nat.le_trans hij hjk) = mapLE M N hjk ≫ mapLE M N hij := sorry

/-- The adjacent transition of the represented relative derived tensor tower. -/
noncomputable abbrev step
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    (n : ℕ) : stage M N (n + 1) ⟶ stage M N n :=
  mapLE M N (Nat.le_add_right n 1)

/-- The canonical tensor tower associated to a global derived right system and an ordinary left
DG-module system. -/
@[stacks 0GZI "relative derived tensor tower of an ordinary left module system"]
noncomputable def tower
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) :=
  Functor.ofOpSequence (X := fun n ↦ stage M N n) (step M N)

/-- Evaluation of the represented relative derived tensor tower. -/
@[simp]
theorem tower_obj
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    (n : ℕ) : (tower M N).obj (op n) = stage M N n := sorry

/-- Every transition of the represented tensor tower is its canonical stagewise tensor map. -/
@[stacks 0GZI "arbitrary transition in a represented relative derived tensor tower"]
theorem tower_transitionMap
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    {i j : ℕ} (hij : i ≤ j) :
    (tower M N).transitionMap hij = mapLE M N hij := sorry

/-- The stage comparisons commute with every morphism of the indexing category. -/
theorem stageIso_naturality
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A)
    {i j : ℕᵒᵖ} (f : i ⟶ j) :
    (DifferentialGradedModule.InverseSystem.TensorProduct.Derived.tower M
          ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N)).map f ≫
        (stageIso M N j.unop).hom =
      (stageIso M N i.unop).hom ≫ (tower M N).map f := sorry

/-- The global-derived and source-shaped constructions give canonically isomorphic relative
derived tensor towers. -/
@[stacks 0GZI "comparison of global and represented relative derived tensor towers"]
noncomputable def towerIso
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A) :
    DifferentialGradedModule.InverseSystem.TensorProduct.Derived.tower M
        ((DifferentialGradedModule.InverseSystem.Derived.Left.Q A).obj N) ≅
      tower M N :=
  NatIso.ofComponents (fun n ↦ stageIso M N n.unop) (stageIso_naturality M N)

/-- The forward component of the global-to-represented tower comparison is the stage
comparison. -/
@[simp]
theorem towerIso_hom_app
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A) (n : ℕ) :
    (towerIso M N).hom.app (op n) = (stageIso M N n).hom := sorry

/-- The inverse component of the global-to-represented tower comparison is the inverse stage
comparison. -/
@[simp]
theorem towerIso_inv_app
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.LeftSystem.{u, x, w} A) (n : ℕ) :
    (towerIso M N).inv.app (op n) = (stageIso M N n).inv := sorry

end RepresentedLeft

/-- The stagewise action of a morphism in the right global derived module category. -/
noncomputable def mapRightApp
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') (n : ℕ) : stage M N n ⟶ stage M' N n :=
  ((DifferentialGradedModule.TensorProduct.Derived.functor (A.obj (op n))).map
    ((DifferentialGradedModule.InverseSystem.Derived.eval A n).map f)).app
      ((DifferentialGradedModule.InverseSystem.Derived.Left.eval A n).obj N)

/-- Stagewise right-factor maps commute with adjacent tensor-tower transitions. -/
theorem mapRightApp_naturality
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') (n : ℕ) :
    (tower M N).stepMap n ≫ mapRightApp N f n =
      mapRightApp N f (n + 1) ≫ (tower M' N).stepMap n := sorry

/-- A morphism of right global derived systems acts on their tensor towers. -/
noncomputable def mapRight
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') : tower M N ⟶ tower M' N :=
  NatTrans.ofOpSequence (mapRightApp N f) (mapRightApp_naturality N f)

/-- The component of the tower map induced by a right-system morphism is its stagewise derived
tensor map. -/
@[simp]
theorem mapRight_app
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') (n : ℕ) :
    (mapRight N f).app (op n) = mapRightApp N f n := sorry

/-- Stagewise right-factor maps commute with every tensor-tower transition. -/
theorem mapRightApp_naturalityLE
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M') {i j : ℕ} (hij : i ≤ j) :
    (tower M N).transitionMap hij ≫ mapRightApp N f i =
      mapRightApp N f j ≫ (tower M' N).transitionMap hij := sorry

/-- The identity right-system morphism induces the identity tensor-tower map. -/
@[simp]
theorem mapRight_id
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A) :
    mapRight N (𝟙 M) = 𝟙 (tower M N) := sorry

/-- Tensor-tower maps in the right factor preserve composition. -/
@[simp]
theorem mapRight_comp
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A)
    {L M P : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : L ⟶ M) (g : M ⟶ P) :
    mapRight N (f ≫ g) = mapRight N f ≫ mapRight N g := sorry

/-- The stagewise action of a morphism in the left global derived module category. -/
noncomputable def mapLeftApp
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (g : N ⟶ N') (n : ℕ) : stage M N n ⟶ stage M N' n :=
  ((DifferentialGradedModule.TensorProduct.Derived.functor (A.obj (op n))).obj
    ((DifferentialGradedModule.InverseSystem.Derived.eval A n).obj M)).map
      ((DifferentialGradedModule.InverseSystem.Derived.Left.eval A n).map g)

/-- Stagewise left-factor maps commute with adjacent tensor-tower transitions. -/
theorem mapLeftApp_naturality
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (g : N ⟶ N') (n : ℕ) :
    (tower M N).stepMap n ≫ mapLeftApp M g n =
      mapLeftApp M g (n + 1) ≫ (tower M N').stepMap n := sorry

/-- A morphism of left global derived systems acts on their tensor towers. -/
noncomputable def mapLeft
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (g : N ⟶ N') : tower M N ⟶ tower M N' :=
  NatTrans.ofOpSequence (mapLeftApp M g) (mapLeftApp_naturality M g)

/-- The component of the tower map induced by a left-system morphism is its stagewise derived
tensor map. -/
@[simp]
theorem mapLeft_app
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (g : N ⟶ N') (n : ℕ) :
    (mapLeft M g).app (op n) = mapLeftApp M g n := sorry

/-- Stagewise left-factor maps commute with every tensor-tower transition. -/
theorem mapLeftApp_naturalityLE
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (g : N ⟶ N') {i j : ℕ} (hij : i ≤ j) :
    (tower M N).transitionMap hij ≫ mapLeftApp M g i =
      mapLeftApp M g j ≫ (tower M N').transitionMap hij := sorry

/-- The identity left-system morphism induces the identity tensor-tower map. -/
@[simp]
theorem mapLeft_id
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A) :
    mapLeft M (𝟙 N) = 𝟙 (tower M N) := sorry

/-- Tensor-tower maps in the left factor preserve composition. -/
@[simp]
theorem mapLeft_comp
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {L N P : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (f : L ⟶ N) (g : N ⟶ P) :
    mapLeft M (f ≫ g) = mapLeft M f ≫ mapLeft M g := sorry

/-- The right and left actions on stagewise relative derived tensor towers commute. -/
theorem mapRight_mapLeft
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (f : M ⟶ M') (g : N ⟶ N') :
    mapRight N f ≫ mapLeft M' g = mapLeft M g ≫ mapRight N' f := sorry

/-- Stagewise relative derived tensor towers are functorial in both global derived module
systems. -/
@[stacks 0GZI "bifunctor of stagewise relative derived tensor towers"]
noncomputable def functor
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R)) :
    DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A ⥤
      DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A ⥤
        SequentialInverseSystem (DerivedCategory (ModuleCat.{max v w} R)) where
  obj M :=
    { obj := tower M
      map := mapLeft M
      map_id := sorry
      map_comp := sorry }
  map f :=
    { app := fun N ↦ mapRight N f
      naturality := sorry }
  map_id := sorry
  map_comp := sorry

/-- Evaluating the tensor-tower bifunctor gives the canonical stagewise tensor tower. -/
@[simp]
theorem functor_obj_obj
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A) :
    ((functor A).obj M).obj N = tower M N := sorry

/-- The outer action of the tensor-tower bifunctor is the canonical right-factor tower map. -/
@[simp]
theorem functor_map_app
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    {M M' : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A}
    (f : M ⟶ M')
    (N : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A) :
    ((functor A).map f).app N = mapRight N f := sorry

/-- The inner action of the tensor-tower bifunctor is the canonical left-factor tower map. -/
@[simp]
theorem functor_obj_map
    (A : SequentialInverseSystem (CochainDGAlgebra.{u, x} R))
    (M : DifferentialGradedModule.InverseSystem.Derived.Category.{u, x, v} A)
    {N N' : DifferentialGradedModule.InverseSystem.Derived.Left.Category.{u, x, w} A}
    (g : N ⟶ N') :
    ((functor A).obj M).map g = mapLeft M g := sorry

end DifferentialGradedModule.InverseSystem.TensorProduct.Derived
