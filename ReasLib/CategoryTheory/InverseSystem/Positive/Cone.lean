module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Positive.Limits

/-!
# Cones over Positive Inverse Systems

This leaf presents limit projections, natural-transformation components, and cone legs for
positive inverse systems through positive stages.  The implementation uses the order-dual index
internally, while the public API is expressed in terms of `PNatInverseSystem.stage`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.PNatInverseSystem

variable {C : Type u} [Category.{v} C]

/-- The canonical projection from the limit of a positive inverse system to its stage `n`. -/
abbrev limitProjection (F : PNatInverseSystem C) [HasLimit F] (n : ℕ+) :
    limit F ⟶ F.stage n :=
  limit.π F (OrderDual.toDual n)

namespace NatTrans

variable {F G : PNatInverseSystem C}

/-- The component at positive stage `n` of a natural transformation of positive inverse systems. -/
abbrev stageMap (f : F ⟶ G) (n : ℕ+) :
    F.stage n ⟶ G.stage n :=
  f.app (OrderDual.toDual n)

end NatTrans

namespace Cone

variable {F : PNatInverseSystem C}

/-- The map from the vertex of a cone over a positive inverse system to its stage `n`. -/
abbrev stageMap (s : Limits.Cone F) (n : ℕ+) :
    s.pt ⟶ F.stage n :=
  s.π.app (OrderDual.toDual n)

/-- The stage maps of a cone over a positive inverse system commute with every transition map. -/
theorem stageMap_naturality (s : Limits.Cone F) {i j : ℕ+} (hij : i ≤ j) :
    stageMap s j ≫ F.transitionMap hij = stageMap s i := sorry

/-- The stage maps of a cone over a positive inverse system commute with each successor map. -/
theorem stageMap_step (s : Limits.Cone F) (n : ℕ+) :
    stageMap s (n + 1) ≫ F.stepMap n = stageMap s n := sorry

end Cone

end CategoryTheory.PNatInverseSystem
