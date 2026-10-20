module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage

/-!
# Base-change structure-sheaf isomorphisms for morphisms of algebraic spaces

The hypothesis that every base change of `f : X ⟶ B` along a scheme over `B`
has `O_T ⟶ f_{T,*} O_{X_T}` an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The hypothesis that every base change `f_T : X_T ⟶ T` along a scheme `T`
over `B` has `O_T ⟶ f_{T,*} O_{X_T}` an isomorphism. -/
class IsIsoBaseChangeStructurePushforward {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) : Prop where
  /-- Every base change along a scheme over `B` induces an isomorphism of
  structure sheaves. -/
  isIso_baseChange :
    ∀ τ : CohStack.SchemesOver B, IsIso (structureSheafMap (CohStack.fiberToBase f τ))

/-- The identity morphism satisfies the base-change structure-sheaf isomorphism
hypothesis. -/
instance instIsIsoBaseChangeStructurePushforwardId {S : Scheme.{u}}
    (X : AlgebraicSpace S) : IsIsoBaseChangeStructurePushforward (𝟙 X) := sorry

/-- The structure-sheaf map of a base change is an isomorphism under the named
hypothesis. -/
instance instIsIso_structureSheafMap {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [IsIsoBaseChangeStructurePushforward f]
    (τ : CohStack.SchemesOver B) :
    IsIso (structureSheafMap (CohStack.fiberToBase f τ)) :=
  IsIsoBaseChangeStructurePushforward.isIso_baseChange τ

/-- The base-change structure-sheaf hypothesis is the pointwise isomorphism
`O_T ⟶ f_{T,*} O_{X_T}` for every scheme `T` over `B`. -/
theorem isIsoBaseChangeStructurePushforward_iff {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) :
    IsIsoBaseChangeStructurePushforward f ↔
      ∀ τ : CohStack.SchemesOver B,
        IsIso (structureSheafMap (CohStack.fiberToBase f τ)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
