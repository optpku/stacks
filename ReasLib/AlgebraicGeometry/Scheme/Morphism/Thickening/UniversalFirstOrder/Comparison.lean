/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Rebase
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.IsUniversalFirstOrder

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (T : Thickening.Over X) (U : Thickening.Over Y)
  [IsFirstOrderThickening ((CategoryTheory.Over.forget X).map T.hom)]
  [IsUniversalFirstOrder U]
  (f : T.left.left ⟶ U.left.left) (sq : CommSq f T.left.hom U.left.hom g)

/-- The canonical comparison from a rebased first-order thickening to a universal first-order
thickening, extending a prescribed map on closed parts. -/
noncomputable def comparison : (Thickening.Over.map g).obj T ⟶ U :=
  lift ((Thickening.Over.map g).obj T) (CategoryTheory.Over.homMk f sq.w)

/-- The canonical comparison restricts to the prescribed map on the closed parts. -/
theorem comparison_left : (comparison g T U f sq).left.left = f := sorry

/-- The closed and ambient components of the canonical comparison form a commutative square. -/
theorem comparison_comm :
    f ≫ U.hom.left = T.hom.left ≫ (comparison g T U f sq).right.left := sorry

/-- The ambient component of the canonical comparison is a morphism over the rebasing map. -/
theorem comparison_over :
    (comparison g T U f sq).right.left ≫ U.right.hom = T.right.hom ≫ g := sorry

/-- The canonical comparison is the unique morphism of thickenings whose closed-part map is
the prescribed map. -/
theorem comparison_unique (k : (Thickening.Over.map g).obj T ⟶ U)
    (hk : k.left.left = f) : k = comparison g T U f sq := sorry

end AlgebraicGeometry.Thickening.IsUniversalFirstOrder
