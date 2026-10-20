module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Tail

/-!
# Truncation of Total Finite Postnikov Systems

This leaf owns the tail functor on total finite Postnikov systems and its
object and morphism computations. Compatibility with the forgetful functor is
developed in `Total.Tail.Forget`.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

/-- Remove the first stage from an object of the total category of finite Postnikov systems. -/
@[stacks 0D7Z "tail of a total finite Postnikov system"]
def tailObj {n : ℕ} (P : Total D (n + 1)) : Total D n where
  base := P.base.δ₀
  system := P.system.tail

/-- Remove the first stage from a morphism in the total category of finite Postnikov systems. -/
@[stacks 0D7Z "tail of a total finite Postnikov-system morphism"]
def tailMap {n : ℕ} {P Q : Total D (n + 1)} (f : P ⟶ Q) :
    tailObj P ⟶ tailObj Q where
  base := ComposableArrows.δ₀Functor.map f.base
  systemMap := PostnikovSystem.Morphism.tail f.systemMap

/-- Truncating the identity total morphism gives the identity of the truncated object. -/
@[simp, stacks 0D7Z]
theorem tailMap_id {n : ℕ} (P : Total D (n + 1)) :
    tailMap (𝟙 P) = 𝟙 (tailObj P) := sorry

/-- Truncating total morphisms preserves their composition. -/
@[simp, stacks 0D7Z]
theorem tailMap_comp {n : ℕ} {P Q R : Total D (n + 1)}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    tailMap (f ≫ g) = tailMap f ≫ tailMap g := sorry

variable (D) in
/-- The tail functor removes the first stage of a finite Postnikov system together with the
corresponding components of every compatible morphism. -/
@[stacks 0D7Z "tail functor on total finite Postnikov systems"]
def tail (n : ℕ) : Total D (n + 1) ⥤ Total D n where
  obj := tailObj
  map := tailMap
  map_id := tailMap_id
  map_comp := tailMap_comp

/-- The base of a truncated total object is the truncated underlying row. -/
@[simp, stacks 0D7Z]
theorem tail_obj_base {n : ℕ} (P : Total D (n + 1)) :
    ((tail D n).obj P).base = P.base.δ₀ := sorry

/-- The system of a truncated total object is the recursive tail of its system. -/
@[simp, stacks 0D7Z]
theorem tail_obj_system {n : ℕ} (P : Total D (n + 1)) :
    ((tail D n).obj P).system = P.system.tail := sorry

/-- The base component of a truncated total morphism is obtained by row truncation. -/
@[simp, stacks 0D7Z]
theorem tail_map_base {n : ℕ} {P Q : Total D (n + 1)} (f : P ⟶ Q) :
    ((tail D n).map f).base = ComposableArrows.δ₀Functor.map f.base := sorry

/-- The system component of a truncated total morphism is the tail of its system map. -/
@[simp, stacks 0D7Z]
theorem tail_map_systemMap {n : ℕ} {P Q : Total D (n + 1)} (f : P ⟶ Q) :
    ((tail D n).map f).systemMap = PostnikovSystem.Morphism.tail f.systemMap := sorry

end CategoryTheory.PostnikovSystem.Total
