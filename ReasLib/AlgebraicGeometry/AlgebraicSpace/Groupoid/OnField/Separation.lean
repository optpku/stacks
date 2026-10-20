module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Separation.Field

/-! Absolute separatedness of decent arrow spaces of groupoids on fields. -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A groupoid on a field with decent arrow space has absolutely separated arrow space. -/
theorem isAbsolutelySeparated {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) [IsOnField G σ] [AlgebraicSpace.IsDecent G.R.left] :
    AlgebraicSpace.IsAbsolutelySeparated G.R.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
