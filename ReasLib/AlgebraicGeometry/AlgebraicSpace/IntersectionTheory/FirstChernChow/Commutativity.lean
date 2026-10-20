module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow

/-! Commutativity of first-Chern cap operations on Chow groups. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
namespace FirstChernChow

/-- Composing first-Chern cap operations in either order gives the same Chow
class after lowering the degree twice. -/
theorem cap_comm {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L N : X.Modules) [isInvertibleObject L] [isInvertibleObject N]
    (k : ℤ) (α : Hom.chowGroup f δ (k + 1 + 1)) :
    cap f δ L k (cap f δ N (k + 1) α) =
      cap f δ N k (cap f δ L (k + 1) α) :=
  sorry

end FirstChernChow
end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
