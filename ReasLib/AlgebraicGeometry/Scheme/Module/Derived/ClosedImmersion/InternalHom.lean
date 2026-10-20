module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ClosedImmersion.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Immersion

@[expose] public section

/-!
# Derived internal Hom for a closed immersion of schemes

This module specializes the derived internal-Hom comparison for closed immersions of ringed
spaces to closed immersions of schemes.
-/

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.ClosedImmersion

/-- For a closed immersion of schemes, derived pushforward of internal Hom from the source
structure sheaf is objectwise isomorphic to the ambient derived internal Hom from its direct
image. -/
theorem pushforwardRHomStructureSheaf_isomorphic
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    IsIsomorphic
      ((RingedSpace.ModuleDerived.ClosedImmersion.pushforwardRHomStructureSheaf
        i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj K)
      ((RingedSpace.ModuleDerived.ClosedImmersion.ambientRHomStructureSheaf
        i.toShHom (IsClosedImmersion.isClosedEmbedding i)).obj K) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.ClosedImmersion
