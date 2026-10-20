module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Separation

/-!
# Separated functors on schemes over an algebraic space

A functor on `(SchemeOver B)ᵒᵖ` is separated over `B` when its product diagonal
is a closed immersion.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

#check (AlgebraicGeometry.AlgebraicSpace.Quot.IsSeparatedOver :
  ((SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.Quot.isSeparatedOver_iff :
  ∀ (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)),
    IsSeparatedOver F ↔ SchemeOver.IsClosedImmersion (Limits.diag F))

end AlgebraicGeometry.AlgebraicSpace.Quot
