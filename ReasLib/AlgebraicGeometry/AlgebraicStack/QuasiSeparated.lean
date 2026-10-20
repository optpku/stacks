module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Absolutely quasi-separated algebraic stacks

An algebraic stack is quasi-separated when its diagonal over `Spec ℤ` is
quasi-compact and quasi-separated as a morphism representable by algebraic spaces.
The absolute base is obtained by postcomposing its projection along the unique
morphism from its base scheme to `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- View a groupoid fibration over `S` as a groupoid fibration over `Spec ℤ`
along the unique morphism `S ⟶ Spec ℤ`. -/
def viewedOverSpecZ {S : Scheme.{u}} (X : GroupoidsOver S) :
    GroupoidsOver (Spec (.of (ULift.{u} ℤ))) :=
  viewedOver (specULiftZIsTerminal.from S) X

/-- The projection of `viewedOverSpecZ X` is `X.p` followed by `Over.map` of the
unique morphism `S ⟶ Spec ℤ`. -/
theorem viewedOverSpecZ_p {S : Scheme.{u}} (X : GroupoidsOver S) :
    (viewedOverSpecZ X).p = X.p ⋙ Over.map (specULiftZIsTerminal.from S) :=
  sorry

/-- An algebraic stack is quasi-separated if, after viewing over `Spec ℤ`, the
diagonal is quasi-compact and quasi-separated as a morphism representable by
algebraic spaces. -/
@[mk_iff]
class IsQuasiSeparated {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- The absolute diagonal is quasi-compact on every scheme-slice representing morphism. -/
  quasiCompact_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))
  /-- The absolute diagonal is quasi-separated on every scheme-slice representing morphism. -/
  quasiSeparated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))

namespace IsQuasiSeparated

/-- A quasi-separated algebraic stack has quasi-compact and quasi-separated
absolute diagonal. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiSeparated X] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)) :=
  sorry

/-- Quasi-compactness and quasi-separatedness of the absolute diagonal witness
that an algebraic stack is quasi-separated. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X)))
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated (Spec (.of (ULift.{u} ℤ))))
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (viewedOverSpecZ X))) :
    IsQuasiSeparated X := sorry

end IsQuasiSeparated

/-- The canonical slice of an absolutely quasi-separated scheme is a
quasi-separated algebraic stack. -/
instance instIsQuasiSeparated_slice {S : Scheme.{u}} (U : Over S)
    [QuasiSeparatedSpace U.left] :
    IsQuasiSeparated (GroupoidsOver.slice U) := sorry

end AlgebraicGeometry.AlgebraicStack
