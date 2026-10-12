/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic

/-!
# A displayed cell replacement, with its original augmentation

Given F→K, attach in degree n the free presheaf on local pairs (x,y) satisfying
dx=phi(y) and dy=0. Its differential is y and its augmentation is x. Start
from zero and take the countable colimit. This simultaneously supplies cycles
and kills every augmentation-kernel cycle at the following stage. No complex,
map or generator is selected from a resolution-existence theorem.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
noncomputable section
universe u

namespace PresheafOfModules.CellReplacement

variable {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})

abbrev Complex := CochainComplex (PresheafOfModules.{u} R) ℤ

variable {R} {F K : Complex R} (φ : F ⟶ K)

/-- The literal local attaching data, including the original comparison. -/
structure Cell (n : ℤ) (U : Cᵒᵖ) : Type u where
  x : (K.X n).obj U
  y : (F.X (n + 1)).obj U
  dx : (K.d n (n + 1)).app U x = (φ.f (n + 1)).app U y
  dy : (F.d (n + 1) ((n + 1) + 1)).app U y = 0

/-- Restriction is the original restriction on the two specified coordinates. -/
def restrictCell (n : ℤ) {U V : Cᵒᵖ} (f : U ⟶ V) (c : Cell φ n U) : Cell φ n V where
  x := (K.X n).map f c.x
  y := (F.X (n + 1)).map f c.y
  dx := by sorry
  dy := by sorry

def cells (n : ℤ) : Cᵒᵖ ⥤ Type u where
  obj U := Cell φ n U
  map f := ↾restrictCell φ n f
  map_id := by sorry
  map_comp := by sorry

def freeCells (n : ℤ) : PresheafOfModules.{u} R := freeObj (R := R) (cells φ n)

/-- Send each actual free generator to its first coordinate x. -/
def evaluateX (n : ℤ) : freeCells φ n ⟶ K.X n :=
  freeObjDesc {
    app U := ↾fun c : Cell φ n U => c.x
    naturality := by sorry }

/-- Send each actual free generator to its boundary coordinate y. -/
def evaluateY (n : ℤ) : freeCells φ n ⟶ F.X (n + 1) :=
  freeObjDesc {
    app U := ↾fun c : Cell φ n U => c.y
    naturality := by sorry }

def nextTerm (n : ℤ) : PresheafOfModules.{u} R := F.X n ⊞ freeCells φ n

/-- The attached-cell differential: old differential on the first summand,
the specified y on the new generators, and no new-component contribution. -/
def nextDifferential (n : ℤ) : nextTerm φ n ⟶ nextTerm φ (n + 1) :=
  biprod.desc (F.d n (n + 1) ≫ biprod.inl) (evaluateY φ n ≫ biprod.inl)

theorem nextDifferential_sq (n : ℤ) :
    nextDifferential φ n ≫ nextDifferential φ (n + 1) = 0 := by
  sorry

def nextComplex : Complex R :=
  CochainComplex.of (nextTerm φ) (nextDifferential φ) (nextDifferential_sq φ)

def nextAugmentation : nextComplex φ ⟶ K where
  f n := biprod.desc (φ.f n) (evaluateX φ n)
  comm' := by sorry

def inclusion : F ⟶ nextComplex φ where
  f _ := biprod.inl
  comm' := by sorry

theorem inclusion_augmentation : inclusion φ ≫ nextAugmentation φ = φ := by
  ext n : 1
  exact biprod.inl_desc (φ.f n) (evaluateX φ n)

/-- The augmentation sends every new generator to its prescribed x. -/
theorem augmentation_generator (n : ℤ) (U : Cᵒᵖ) (c : Cell φ n U) :
    ((biprod.inr : freeCells φ n ⟶ nextTerm φ n) ≫ (nextAugmentation φ).f n).app U
      (ModuleCat.freeMk c) = c.x := by
  exact (congrArg (fun f : freeCells φ n ⟶ K.X n => f.app U (ModuleCat.freeMk c))
    (biprod.inr_desc (φ.f n) (evaluateX φ n))).trans (ModuleCat.freeDesc_apply _ _)

/-- A stage stores its real map to the original K. -/
structure Stage (K : Complex R) where
  complex : Complex R
  augmentation : complex ⟶ K

def Stage.next (s : Stage K) : Stage K := ⟨nextComplex s.augmentation, nextAugmentation s.augmentation⟩

def seed (K : Complex R) : Stage K := ⟨0, 0⟩

def stage (K : Complex R) : ℕ → Stage K
  | 0 => seed K
  | n + 1 => (stage K n).next

def transition (K : Complex R) (n : ℕ) : (stage K n).complex ⟶ (stage K (n + 1)).complex :=
  inclusion (stage K n).augmentation

def diagram (K : Complex R) : ℕ ⥤ Complex R := Functor.ofSequence (transition K)

/-- The explicit colimit of the displayed attaching tower. -/
def replacement (K : Complex R) : Complex R := colimit (diagram K)

def augmentationCocone (K : Complex R) : Cocone (diagram K) where
  pt := K
  ι := NatTrans.ofSequence (fun n => (stage K n).augmentation) (by
    intro n
    exact (congrArg (fun f => f ≫ (stage K (n + 1)).augmentation)
      (Functor.ofSequence_map_homOfLE_succ (transition K) n)).trans
        ((inclusion_augmentation (stage K n).augmentation).trans (Category.comp_id _).symm))

/-- The canonical comparison to the original input, not an arbitrary quasi-isomorphism. -/
def augmentation (K : Complex R) : replacement K ⟶ K :=
  colimit.desc (diagram K) (augmentationCocone K)

theorem stage_augmentation (K : Complex R) (n : ℕ) :
    colimit.ι (diagram K) n ≫ augmentation K = (stage K n).augmentation :=
  colimit.ι_desc _ _

/-- Every target cycle is added at stage1; every source cycle in the kernel
of augmentation is killed by its displayed (boundary,cycle) cell at the next
stage. Filtered colimits of modules are exact, degree by degree. -/
theorem augmentation_quasiIso (K : Complex R) : QuasiIso (augmentation K) := by
  sorry

end PresheafOfModules.CellReplacement
