/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functoriality of Sequential Derived Limits

TR3 extends a commuting square between the Milnor difference maps of two
chosen derived-limit triangles to a morphism of triangles. The first component
is generally nonunique, so this leaf exposes existence statements rather than
choosing a map between derived limits.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

namespace HasMilnorTriangle

/-- Stacks 0H9J: a commuting square between the middle maps of two chosen
Milnor triangles extends to a morphism of triangles with the prescribed second
and third components. No uniqueness of the first component is asserted. -/
@[stacks 0H9J]
theorem existsTriangleMorphism
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K L : D}
    (hK : HasMilnorTriangle Ksys K) (hL : HasMilnorTriangle Lsys L)
    {a₂ a₃ : ∏ᶜ Ksys.family ⟶ ∏ᶜ Lsys.family}
    (hcomm : CommSq Ksys.milnorDifferenceMap a₂ a₃ Lsys.milnorDifferenceMap) :
    ∃ f : hK.triangle ⟶ hL.triangle, f.hom₂ = a₂ ∧ f.hom₃ = a₃ := sorry

namespace Morphism

/-- A morphism of sequential inverse systems induces equal product maps that
extend to a morphism between any chosen Milnor triangles. -/
@[stacks 0H9J]
theorem exists_of_hom
    {Ksys Lsys : SequentialInverseSystem D}
    [HasProduct Ksys.family] [HasProduct Lsys.family] {K L : D}
    (hK : HasMilnorTriangle Ksys K) (hL : HasMilnorTriangle Lsys L)
    (φ : Ksys ⟶ Lsys) :
    ∃ f : hK.triangle ⟶ hL.triangle,
      f.hom₂ = SequentialInverseSystem.productMap φ ∧
        f.hom₃ = SequentialInverseSystem.productMap φ := sorry

end Morphism

end HasMilnorTriangle

namespace IsDerivedLimit

/-- A morphism of sequential inverse systems induces at least one morphism
between chosen derived limits, compatible with every stage projection. The
induced morphism is not declared canonical. -/
@[stacks 0H9J]
theorem existsMap {Ksys Lsys : SequentialInverseSystem D} {K L : D}
    (hK : IsDerivedLimit Ksys K) (hL : IsDerivedLimit Lsys L)
    (φ : Ksys ⟶ Lsys) :
    ∃ f : K ⟶ L, ∀ n : ℕ,
      f ≫ hL.stageProjection n = hK.stageProjection n ≫ φ.app (op n) := sorry

end IsDerivedLimit

end

end CategoryTheory
