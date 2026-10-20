module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable

/-!
# Fibre products along Yoneda sections

A morphism of presheaves representable by algebraic spaces pulls back along a
scheme Yoneda section to an algebraic space and a structure morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace representableByAlgebraicSpaces

/-- The algebraic space `U ×_G F` obtained by pulling a morphism representable by
algebraic spaces back along a Yoneda section `ξ : yoneda.obj U ⟶ G`. -/
def pullbackSpace {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    AlgebraicSpace S :=
  ofFunctor (pullback ξ a) (ha.isAlgebraicSpace_pullback ξ).isSheaf
    (ha.isAlgebraicSpace_pullback ξ).representableDiagonal
    (ha.isAlgebraicSpace_pullback ξ).atlas

/-- The functor of points of the fibre product algebraic space along a Yoneda
section is the fibre product of functors. -/
theorem pullbackSpace_functorOfPoints {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    (pullbackSpace ha ξ).functorOfPoints = pullback ξ a :=
  sorry

/-- The structure morphism `U ×_G F ⟶ U` of the fibre product algebraic space
along a Yoneda section, given by the first projection of the fibre product of
functors. -/
def pullbackHom {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    pullbackSpace ha ξ ⟶ ofOver U :=
  pullback.fst ξ a

/-- The structure morphism of the fibre product algebraic space is the first
projection of the fibre product of functors. -/
theorem pullbackHom_fst {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (ha : representableByAlgebraicSpaces a) {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    pullbackHom ha ξ = pullback.fst ξ a :=
  sorry

end representableByAlgebraicSpaces

end AlgebraicGeometry.AlgebraicSpace
