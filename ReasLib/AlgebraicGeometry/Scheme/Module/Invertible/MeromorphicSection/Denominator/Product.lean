module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator
public import ReasLib.Topology.NowhereDense.FiniteUnion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Products with denominator ideals

This file constructs the product of the denominator ideal of a meromorphic
section with a module sheaf and the two canonical maps out of that product.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The union of the supports of the cokernels of the denominator inclusion
and multiplication by the meromorphic section. -/
noncomputable abbrev denominatorSupport
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) : Set X :=
  RingedSpace.moduleSupport (cokernel (denominatorIdealSheaf ℒ s).arrow) ∪
    RingedSpace.moduleSupport (cokernel (denominatorSectionMap ℒ s))

/-- The product `Iℱ` of the denominator ideal `I` of a meromorphic section
with a module sheaf `ℱ`. -/
noncomputable def denominatorIdealProduct
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules) :
    Subobject ℱ :=
  imageSubobject
    (SheafOfModules.RingedSite.IdealSheaf.action (denominatorIdealSheaf ℒ s) ℱ)

/-- The canonical epimorphism from the tensor product `I ⊗ ℱ` onto the
denominator-ideal product `Iℱ`. -/
noncomputable def denominatorIdealProductFactor
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules) :
    Subobject.underlying.obj (denominatorIdealSheaf ℒ s) ⊗ ℱ ⟶
      Subobject.underlying.obj (denominatorIdealProduct ℒ s ℱ) :=
  factorThruImageSubobject
    (SheafOfModules.RingedSite.IdealSheaf.action (denominatorIdealSheaf ℒ s) ℱ)

/-- The tensor map `I ⊗ ℱ ⟶ ℱ ⊗ ℒ` induced by multiplication from the
denominator ideal `I` to the invertible module `ℒ`. -/
noncomputable def denominatorSectionTensorMap
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules) :
    Subobject.underlying.obj (denominatorIdealSheaf ℒ s) ⊗ ℱ ⟶ ℱ ⊗ ℒ :=
  tensorHom (denominatorSectionMap ℒ s) (𝟙 ℱ) ≫ (β_ ℒ ℱ).hom

/-- The canonical factor onto `Iℱ`, followed by its inclusion into `ℱ`, is
the ideal-sheaf action on `ℱ`. -/
theorem denominatorIdealProductFactor_inclusion
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (ℱ : X.Modules) :
    denominatorIdealProductFactor ℒ s ℱ ≫
        (denominatorIdealProduct ℒ s ℱ).arrow =
      SheafOfModules.RingedSite.IdealSheaf.action (denominatorIdealSheaf ℒ s) ℱ := sorry

/-- For a regular meromorphic section, the union of the two denominator
cokernel supports is closed and nowhere dense. -/
theorem denominatorSupport_isClosed_and_isNowhereDense
    [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s) :
    IsClosed (denominatorSupport ℒ s) ∧ IsNowhereDense (denominatorSupport ℒ s) := sorry

/-- If a coherent module sheaf has full support and no embedded associated
points, the inclusion `Iℱ ⟶ ℱ` is monic and its cokernel is supported on the
denominator support. -/
theorem denominatorIdealProductInclusion_mono_and_cokernelSupport
    [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hEmbedded : Scheme.Modules.embeddedAssociatedPoints ℱ = (∅ : Set X))
    (hSupp : RingedSpace.moduleSupport ℱ = Set.univ) :
    Mono (denominatorIdealProduct ℒ s ℱ).arrow ∧
      RingedSpace.moduleSupport (cokernel (denominatorIdealProduct ℒ s ℱ).arrow) ⊆
        denominatorSupport ℒ s := sorry

/-- If a coherent module sheaf has full support and no embedded associated
points, there is a unique monic map `Iℱ ⟶ ℱ ⊗ ℒ` factoring multiplication by
the meromorphic section whose cokernel is supported on the denominator
support. -/
theorem existsUnique_denominatorIdealProductSectionMap
    [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hEmbedded : Scheme.Modules.embeddedAssociatedPoints ℱ = (∅ : Set X))
    (hSupp : RingedSpace.moduleSupport ℱ = Set.univ) :
    ∃! σ : Subobject.underlying.obj (denominatorIdealProduct ℒ s ℱ) ⟶ ℱ ⊗ ℒ,
      denominatorIdealProductFactor ℒ s ℱ ≫ σ =
          denominatorSectionTensorMap ℒ s ℱ ∧
        Mono σ ∧
        RingedSpace.moduleSupport (cokernel σ) ⊆ denominatorSupport ℒ s := sorry

/-- A coherent module sheaf with full support and no embedded associated
points has canonical monic maps `Iℱ ⟶ ℱ` and `Iℱ ⟶ ℱ ⊗ ℒ`, and both
cokernels are supported on the denominator support. -/
theorem denominatorIdealProduct_maps
    [IsLocallyNoetherian X]
    (ℒ : X.Modules) [Scheme.Modules.Invertible ℒ]
    (s : X.toLocallyRingedSpace.meromorphicSections ℒ)
    (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection ℒ s)
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (hEmbedded : Scheme.Modules.embeddedAssociatedPoints ℱ = (∅ : Set X))
    (hSupp : RingedSpace.moduleSupport ℱ = Set.univ) :
    (Mono (denominatorIdealProduct ℒ s ℱ).arrow ∧
      RingedSpace.moduleSupport (cokernel (denominatorIdealProduct ℒ s ℱ).arrow) ⊆
        denominatorSupport ℒ s) ∧
      ∃! σ : Subobject.underlying.obj (denominatorIdealProduct ℒ s ℱ) ⟶ ℱ ⊗ ℒ,
        denominatorIdealProductFactor ℒ s ℱ ≫ σ =
            denominatorSectionTensorMap ℒ s ℱ ∧
          Mono σ ∧
          RingedSpace.moduleSupport (cokernel σ) ⊆ denominatorSupport ℒ s := sorry

end AlgebraicGeometry.Scheme
