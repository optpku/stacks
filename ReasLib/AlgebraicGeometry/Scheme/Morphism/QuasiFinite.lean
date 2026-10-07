module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Quasi-finite scheme morphisms

This file owns the global quasi-finite condition for scheme morphisms. Mathlib's
`LocallyQuasiFinite` records the finite-fibre condition but deliberately does not include local
finite type, so the global notion combines it with the project-level `FiniteType` owner.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A scheme morphism is quasi-finite at a point in the finite-type sense when it is both of
finite type and stalkwise quasi-finite there. -/
def FiniteType.QuasiFiniteAt (x : X) : Prop :=
  f.FiniteTypeAt x ∧ f.QuasiFiniteAt x

/-- Finite-type quasi-finiteness at a point is the conjunction of its two defining conditions. -/
theorem FiniteType.QuasiFiniteAt.iff_finiteTypeAt_and_quasiFiniteAt (x : X) :
    FiniteType.QuasiFiniteAt f x ↔ f.FiniteTypeAt x ∧ f.QuasiFiniteAt x := sorry

/-- Finite-type quasi-finiteness at a point is characterized on compatible affine neighborhoods
by a finite-type ring map that is quasi-finite at the corresponding prime. -/
theorem FiniteType.QuasiFiniteAt.iff_exists_affineNeighborhood (x : X) :
    FiniteType.QuasiFiniteAt f x ↔
      ∃ U : X.affineOpens, ∃ hxU : x ∈ (U : X.Opens),
        ∃ V : S.affineOpens, ∃ e : U ≤ f ⁻¹ᵁ V,
          (CommRingCat.Hom.hom (f.appLE V U e)).FiniteType ∧
            (CommRingCat.Hom.hom (f.appLE V U e)).QuasiFiniteAt
              (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := sorry

/-- Local finite type together with local quasi-finiteness is equivalent to finite-type
quasi-finiteness at every source point. -/
@[stacks 01TD]
theorem FiniteType.locallyQuasiFinite_iff_forall_quasiFiniteAt :
    LocallyOfFiniteType f ∧ LocallyQuasiFinite f ↔
      ∀ x : X, FiniteType.QuasiFiniteAt f x := sorry

/-- A scheme morphism is quasi-finite when it is of finite type and locally quasi-finite. -/
@[stacks 01TD]
class QuasiFinite : Prop extends FiniteType f, LocallyQuasiFinite f

/-- Finite type together with local quasi-finiteness canonically supplies quasi-finiteness. -/
instance instQuasiFinite [FiniteType f] [LocallyQuasiFinite f] :
    QuasiFinite f := sorry

/-- A quasi-finite morphism is of finite type. -/
instance instFiniteTypeOfQuasiFinite [QuasiFinite f] :
    FiniteType f := sorry

/-- A quasi-finite morphism is quasi-compact. -/
instance instQuasiCompactOfQuasiFinite [QuasiFinite f] :
    QuasiCompact f := sorry

/-- A quasi-finite morphism is locally of finite type. -/
instance instLocallyOfFiniteTypeOfQuasiFinite [QuasiFinite f] :
    LocallyOfFiniteType f := sorry

/-- A quasi-finite morphism satisfies mathlib's local quasi-finiteness condition. -/
instance instLocallyQuasiFiniteOfQuasiFinite [QuasiFinite f] :
    LocallyQuasiFinite f := sorry

/-- Quasi-finite structures are proposition-valued. -/
instance instSubsingletonQuasiFinite :
    Subsingleton (QuasiFinite f) := inferInstance

/-- The defining condition for a quasi-finite scheme morphism. -/
@[stacks 01TD]
theorem quasiFinite_iff :
    QuasiFinite f ↔ FiniteType f ∧ LocallyQuasiFinite f := sorry

/-- A morphism is quasi-finite exactly when it is of finite type and every source point is
isolated in its fibre. -/
theorem quasiFinite_iff_finiteType_and_isOpen_singleton_asFiber :
    QuasiFinite f ↔
      FiniteType f ∧ ∀ x : X, IsOpen ({f.asFiber x} : Set (f.fiber (f x))) := sorry

/-- A quasi-finite morphism is equivalently quasi-compact, locally of finite type, and locally
quasi-finite in mathlib's finite-fibre sense. -/
@[stacks 01TJ]
theorem quasiFinite_iff_quasiCompact_locallyOfFiniteType_and_locallyQuasiFinite :
    QuasiFinite f ↔
      QuasiCompact f ∧ LocallyOfFiniteType f ∧ LocallyQuasiFinite f := sorry

/-- Construct a quasi-finite morphism from its quasi-compact, local finite-type, and local
quasi-finiteness components. -/
theorem quasiFinite_of_quasiCompact_of_locallyOfFiniteType_of_locallyQuasiFinite
    (hqc : QuasiCompact f) (hlft : LocallyOfFiniteType f) (hlqf : LocallyQuasiFinite f) :
    QuasiFinite f := sorry

/-- Every point of a quasi-finite morphism is a quasi-finite point. -/
theorem quasiFiniteAt_of_quasiFinite [QuasiFinite f] (x : X) :
    f.QuasiFiniteAt x := sorry

/-- Every point of a quasi-finite morphism is a quasi-finite point. -/
theorem QuasiFinite.quasiFiniteAt (hf : QuasiFinite f) (x : X) :
    f.QuasiFiniteAt x := sorry

/-- A quasi-finite morphism is quasi-compact and quasi-finite at every source point. -/
theorem QuasiFinite.quasiCompact_and_forall_quasiFiniteAt (hf : QuasiFinite f) :
    QuasiCompact f ∧ ∀ x : X, f.QuasiFiniteAt x := sorry

/-- A quasi-finite morphism is locally of finite type. -/
theorem QuasiFinite.locallyOfFiniteType (hf : QuasiFinite f) :
    LocallyOfFiniteType f := sorry

/-- A quasi-finite morphism is quasi-compact. -/
theorem QuasiFinite.quasiCompact (hf : QuasiFinite f) :
    QuasiCompact f := sorry

/-- A quasi-finite morphism has finite fibres over all target points. -/
@[stacks 02NH]
theorem QuasiFinite.finiteFibers (hf : QuasiFinite f) :
    ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S)) := sorry

/-- Local finite type, quasi-compactness, and finite fibres imply quasi-finiteness. -/
@[stacks 02NH]
theorem quasiFinite_of_locallyOfFiniteType_of_quasiCompact_of_finiteFibers
    (hlft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hfib : ∀ s : S, Set.Finite ((fun x : X ↦ f x) ⁻¹' ({s} : Set S))) :
    QuasiFinite f := sorry

end Scheme.Hom
end AlgebraicGeometry
