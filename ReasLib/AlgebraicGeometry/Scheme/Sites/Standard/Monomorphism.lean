module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.LowerShriek
public import ReasLib.CategoryTheory.Comma.Over.Mono
public import ReasLib.CategoryTheory.Sites.FullyFaithful

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.StandardTopology.Big

/-- A monomorphism of schemes induces an invertible counit for the cocontinuous
sheaf adjunction on every standard big site. -/
theorem sheafAdjunctionCocontinuous_counit_app_isIso_of_mono
    {X Y : Scheme.{u}} (τ : StandardTopology) (f : X ⟶ Y) [Mono f]
    [∀ P : (Over X)ᵒᵖ ⥤ Type (u + 1),
      (Over.map f).op.HasPointwiseRightKanExtension P]
    (𝒜 : Sheaf (τ.overTopology X) (Type (u + 1))) :
    IsIso
      (((Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
        (τ.overTopology X) (τ.overTopology Y)).counit.app 𝒜) := sorry

end AlgebraicGeometry.StandardTopology.Big
