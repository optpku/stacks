module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Split
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.InverseSystem.EventualZero
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Map

/-!
# Tail Decompositions of Sequential Inverse Systems

An essentially constant sequential inverse system can be described after a finite shift by a
constant limit summand and an eventually vanishing complementary system.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

namespace TailDecomposition

/-- A sequential inverse system has a limit tail decomposition when a shifted tail is identified
stagewise with the binary biproduct of its limit object and an eventually vanishing complementary
inverse system, compatibly with every transition map. -/
def HasLimit (F : SequentialInverseSystem A) : Prop :=
  ∃ c : LimitCone F,
    ∃ n : ℕ,
      ∃ Z : SequentialInverseSystem A,
        ∃ B : ∀ j, BinaryBiproductData c.cone.pt (Z.obj (op j)),
          ∃ e : ∀ j, (F.shift n).obj (op j) ≅ (B j).bicone.pt,
            (∀ j, c.cone.π.app (op (n + j)) = (B j).bicone.inl ≫ (e j).inv) ∧
              (∀ {i j : ℕ} (hij : i ≤ j),
                (F.shift n).transitionMap hij =
                  (e j).hom ≫ BinaryBiproductData.map (B j) (B i) (Z.transitionMap hij) ≫
                (e i).inv) ∧
                PreorderInverseSystem.Transition.EventuallyZero Z

section

variable [Preadditive A]

namespace HasLimit

/-- The eventual split-limit criterion is equivalent to an explicit sequential
tail decomposition with a constant limit summand and eventually vanishing complement. -/
theorem iff_split [IsIdempotentComplete A] (F : SequentialInverseSystem A) :
    EssentiallyConstant.Split.Eventual.HasLimit F ↔ HasLimit F := sorry

/-- A sequential inverse system is essentially constant exactly when it has an
explicit limit tail decomposition. -/
@[stacks 070C]
theorem iff_essentiallyConstant [IsIdempotentComplete A]
    (F : SequentialInverseSystem A) :
    IsCofiltered.IsEssentiallyConstant F ↔ HasLimit F := sorry

end HasLimit

end

end TailDecomposition

end CategoryTheory.SequentialInverseSystem
