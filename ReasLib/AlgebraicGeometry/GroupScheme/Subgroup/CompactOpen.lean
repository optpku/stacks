/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupScheme

variable {k : Type u} [Field k]

/-- A group scheme with finitely many geometric connected components has a compact open and
closed subgroup scheme. -/
theorem existsCompactClopenSubgroup_of_finiteGeometricComponents
    (G : SchemeOverField k) [GrpObj G]
    [Finite (ConnectedComponents
      (FieldExtension.baseChange k (AlgebraicClosure k) G.hom))] :
    ∃ H : Scheme.ClosedSubgroup G,
      IsOpenImmersion H.inclusion.left ∧
        let X := H.left.X
        CompactSpace X.left := sorry

end AlgebraicGeometry.GroupScheme
