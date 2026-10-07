module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.PurelyInseparable
public import ReasLib.FieldTheory.PurelyInseparable.PerfectClosure
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.UniversalHomeomorphism

@[expose] public section

open CategoryTheory
open scoped PerfectClosure

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The base change of a connected scheme to the perfect closure of its base field is
connected. -/
instance instConnectedSpacePerfectClosure
    {k : Type u} [Field k] (X : SchemeOverField k) [ConnectedSpace X.left] :
    ConnectedSpace (FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom) := sorry

/-- The projection from perfect-closure base change of a connected scheme induces a
homeomorphism on étale fundamental groups at every geometric point of the base change. -/
theorem fundamentalGroupIsoPerfectClosure
    {k : Type u} [Field k] (X : SchemeOverField k) [ConnectedSpace X.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom) :
    IsHomeomorph (Scheme.Hom.fundamentalGroupMap
      (FieldExtension.toSource k (kᵖᵉʳᶠ) X.hom) s) := sorry

end AlgebraicGeometry.SchemeOverField
