module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Diagonal

/-!
# Separated functors on schemes over an algebraic space

A functor on `(SchemeOver B)ᵒᵖ` is separated over `B` when its product
diagonal is a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A functor on schemes over `B` is separated over `B` when its product
diagonal is a closed immersion. -/
class IsSeparatedOver (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) : Prop where
  /-- The product diagonal is a closed immersion on schemes over `B`. -/
  isClosedImmersion_diagonal : SchemeOver.IsClosedImmersion (Limits.diag F)

/-- A functor on schemes over `B` is separated over `B` if and only if its
product diagonal is a closed immersion. -/
theorem isSeparatedOver_iff (F : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)) :
    IsSeparatedOver F ↔ SchemeOver.IsClosedImmersion (Limits.diag F) := sorry

/-- The proper-support Quot functor of a quasi-coherent module along a finitely
presented separated morphism of algebraic spaces is separated over the base. -/
instance instIsSeparatedOver (f : X ⟶ B) [FinitePresentation f]
    [Separated f] (F : X.Modules) [F.IsQuasicoherent] :
    IsSeparatedOver (quot f F) := sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
