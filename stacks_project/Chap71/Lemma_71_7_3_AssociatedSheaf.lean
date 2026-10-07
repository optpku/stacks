module

public import stacks_project.Chap71.Definition_71_7_1_AssociatedSheaf

/-!
# Canonical section morphisms of associated sheaves

The unit morphism corresponding to the canonical section `1_D` of `𝒪_X(D)` is
the comparison of `IdealSubobject.canonicalSectionHom` along
`Modules.structureModuleIsoTensorUnit`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The unit morphism corresponding to the canonical section `1_D` of
`associatedSheaf D`, obtained by comparing `IdealSubobject.canonicalSectionHom`
along the structure-module isomorphism with the monoidal unit. -/
noncomputable def canonicalSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    𝟙_ X.Modules ⟶ associatedSheaf D :=
  (Modules.structureModuleIsoTensorUnit X).inv ≫
    IdealSubobject.canonicalSectionHom D.idealSheaf

/-- Comparing `canonicalSectionHom` along the structure-module isomorphism recovers
the canonical global section `1_D`. -/
theorem unitHomEquiv_canonicalSectionHom {S : Scheme.{u}} {X : AlgebraicSpace S}
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    (associatedSheaf D).unitHomEquiv
        ((Modules.structureModuleIsoTensorUnit X).hom ≫ canonicalSectionHom D) =
      canonicalSection D :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
