module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType

/-!
# Finite type scheme morphisms

This file relates the pointwise affine-neighborhood formulation of finite type to local finite
type and packages finite type as local finite type together with quasi-compactness.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A morphism `f : X ⟶ S` is of finite type at `x` if there are affine source and target
neighborhoods on which the induced ring homomorphism is of finite type. -/
def FiniteTypeAt (x : X) : Prop :=
  ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
    ∃ V : S.affineOpens,
      ∃ e : U ≤ f ⁻¹ᵁ V,
        (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType

/-- A proof of finite type at a point supplies affine source and target neighborhoods on which
the induced ring homomorphism is of finite type. -/
theorem FiniteTypeAt.exists_affineNeighborhood {x : X} (h : f.FiniteTypeAt x) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : S.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType := sorry

/-- `FiniteTypeAt f x` is exactly the affine-neighborhood witness condition at `x`. -/
theorem finiteTypeAt_iff (x : X) :
    f.FiniteTypeAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : S.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType := sorry

/-- A morphism is locally of finite type exactly when it is locally of type
`RingHom.FiniteType`. -/
theorem locallyOfFiniteType_iff_locallyOfType :
    LocallyOfFiniteType f ↔ LocallyOfType RingHom.FiniteType f := sorry

/-- Local finite type canonically supplies the corresponding `LocallyOfType` instance. -/
instance instLocallyOfTypeRingHomFiniteTypeOfLocallyOfFiniteType
    [LocallyOfFiniteType f] : LocallyOfType RingHom.FiniteType f :=
  (locallyOfFiniteType_iff_locallyOfType f).mp inferInstance

/-- A morphism is locally of finite type if and only if it is of finite type at every source
point. -/
theorem locallyOfFiniteType_iff_forall_finiteTypeAt :
    LocallyOfFiniteType f ↔ ∀ x : X, f.FiniteTypeAt x := sorry

/-- A scheme morphism is locally of finite type if and only if the target has an open cover whose
pullbacks have open covers by locally finite type morphisms. -/
@[stacks 01T2]
theorem locallyOfFiniteType_iff_exists_openCover :
    LocallyOfFiniteType f ↔
      ∃ 𝒱 : S.OpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
          ∀ i : 𝒰.I₀, LocallyOfFiniteType (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- A scheme morphism is locally of finite type if and only if the target and the pullbacks of its
cover members have affine open covers whose induced maps on global sections are of finite type. -/
@[stacks 01T2]
theorem locallyOfFiniteType_iff_exists_affineOpenCover :
    LocallyOfFiniteType f ↔
      ∃ 𝒱 : S.AffineOpenCover, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
          ∀ i : 𝒰.I₀,
            (CommRingCat.Hom.hom
              (Scheme.Hom.appTop (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j))).FiniteType := sorry

/-- A scheme morphism is of finite type if it is quasi-compact and locally of finite type. -/
class FiniteType : Prop extends QuasiCompact f, LocallyOfFiniteType f

/-- A quasi-compact morphism that is locally of finite type is of finite type. -/
instance instFiniteType [QuasiCompact f] [LocallyOfFiniteType f] : FiniteType f where
  toQuasiCompact := inferInstance
  toLocallyOfFiniteType := inferInstance

/-- A finite type morphism is quasi-compact. -/
instance instQuasiCompactOfFiniteType [h : FiniteType f] :
    QuasiCompact f :=
  h.toQuasiCompact

/-- A finite type morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOfFiniteType [h : FiniteType f] :
    LocallyOfFiniteType f :=
  h.toLocallyOfFiniteType

/-- Finite type structures are proposition-valued. -/
instance instSubsingletonFiniteType :
    Subsingleton (FiniteType f) :=
  inferInstance

/-- `FiniteType f` is equivalent to quasi-compactness together with local finite type. -/
theorem finiteType_iff :
    FiniteType f ↔ QuasiCompact f ∧ LocallyOfFiniteType f := sorry

/-- `FiniteType f` is equivalent to quasi-compactness together with finite type at every source
point. -/
theorem finiteType_iff_quasiCompact_and_forall_finiteTypeAt :
    FiniteType f ↔
      QuasiCompact f ∧ ∀ x : X, f.FiniteTypeAt x := sorry

end Scheme.Hom
end AlgebraicGeometry
