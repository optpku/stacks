module

public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.Irreducible
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents.Locality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero

/-!
# Finite irreducible components on compact opens of algebraic spaces

An algebraic space has finitely many irreducible components on compact opens when some
(equivalently every) surjective étale scheme atlas has that scheme-level property, equivalently
when every quasi-compact étale algebraic space over it has finitely many codimension-0 points
and finitely many irreducible components on its space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every quasi-compact algebraic space étale over `X` has finitely many codimension-`0`
points. -/
def finiteCodimZeroOnEtaleCompact {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
    IsQuasiCompact Y → Etale f → (codimZeroPoints Y).Finite

/-- `finiteCodimZeroOnEtaleCompact X` means every quasi-compact étale `Y ⟶ X` has finitely
many codimension-`0` points. -/
theorem finiteCodimZeroOnEtaleCompact_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    finiteCodimZeroOnEtaleCompact X ↔
      ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X),
        IsQuasiCompact Y → Etale f → (codimZeroPoints Y).Finite :=
  sorry

namespace finiteCodimZeroOnEtaleCompact

/-- A quasi-compact étale morphism into a space satisfying `finiteCodimZeroOnEtaleCompact`
has finitely many codimension-`0` points on its source. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (h : finiteCodimZeroOnEtaleCompact X) [IsQuasiCompact Y] [Etale f] :
    (codimZeroPoints Y).Finite :=
  sorry

end finiteCodimZeroOnEtaleCompact

/-- Every quasi-compact algebraic space étale over `X` has finitely many irreducible
components on its space of points. -/
def finiteIrreducibleComponentsOnEtaleCompact {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  ∀ {Y : AlgebraicSpace S} (f : Y ⟶ X),
    IsQuasiCompact Y → Etale f →
      ∀ (τ : TopologicalSpace (Points Y)),
        IsPointsTopology Y τ → (@irreducibleComponents (Points Y) τ).Finite

/-- `finiteIrreducibleComponentsOnEtaleCompact X` means every quasi-compact étale `Y ⟶ X`
has finitely many irreducible components in every canonical topology on `Points Y`. -/
theorem finiteIrreducibleComponentsOnEtaleCompact_iff {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    finiteIrreducibleComponentsOnEtaleCompact X ↔
      ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X),
        IsQuasiCompact Y → Etale f →
          ∀ (τ : TopologicalSpace (Points Y)),
            IsPointsTopology Y τ → (@irreducibleComponents (Points Y) τ).Finite :=
  sorry

namespace finiteIrreducibleComponentsOnEtaleCompact

/-- A quasi-compact étale morphism into a space satisfying
`finiteIrreducibleComponentsOnEtaleCompact` has finitely many irreducible components on
the source space of points. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (h : finiteIrreducibleComponentsOnEtaleCompact X) [IsQuasiCompact Y] [Etale f]
    {τ : TopologicalSpace (Points Y)} (hτ : IsPointsTopology Y τ) :
    (@irreducibleComponents (Points Y) τ).Finite :=
  sorry

end finiteIrreducibleComponentsOnEtaleCompact

/-- An algebraic space has finitely many irreducible components on compact opens if it
admits a representable étale locally-surjective atlas whose source scheme has finitely many
irreducible components on every quasi-compact open. -/
@[mk_iff]
class HasFiniteIrreducibleComponentsOnCompactOpens {S : Scheme.{u}}
    (X : AlgebraicSpace S) : Prop where
  /-- There is a representable étale locally-surjective atlas from a scheme with finitely
  many irreducible components on compact opens. -/
  exists_finiteComponents_etaleCover :
    existsSurjectiveEtale
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- An algebraic space with finitely many irreducible components on compact opens admits a
representable étale locally-surjective atlas from a scheme with that property. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    existsSurjectiveEtale
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X :=
  sorry

/-- A representable étale locally-surjective atlas from a scheme with finitely many
irreducible components on compact opens witnesses the algebraic-space property. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : existsSurjectiveEtale
      (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X) :
    HasFiniteIrreducibleComponentsOnCompactOpens X :=
  sorry

/-- An algebraic space has finitely many irreducible components on compact opens if and only
if every étale morphism from a scheme has that property on the source. -/
theorem iff_forallEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔
      forallEtale
        (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X :=
  sorry

/-- An algebraic space has finitely many irreducible components on compact opens if and only
if every quasi-compact étale algebraic space over it has finitely many codimension-`0`
points. -/
theorem iff_finiteCodimZeroOnEtaleCompact {S : Scheme.{u}} (X : AlgebraicSpace S) :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔ finiteCodimZeroOnEtaleCompact X :=
  sorry

/-- An algebraic space has finitely many irreducible components on compact opens if and only
if every quasi-compact étale algebraic space over it has finitely many irreducible
components on its space of points. -/
theorem iff_finiteIrreducibleComponentsOnEtaleCompact {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasFiniteIrreducibleComponentsOnCompactOpens X ↔
      finiteIrreducibleComponentsOnEtaleCompact X :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

/-- A scheme over `S` with finitely many irreducible components on compact opens, viewed as
an algebraic space, has that property. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_ofOver {S : Scheme.{u}}
    (T : Over S) [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left] :
    HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T) where
  exists_finiteComponents_etaleCover :=
    existsSurjectiveEtale.of (𝟙 (ofOver T)) (ofOver_id_presheaf_etale T)
      (ofOver_id_locallySurjective T) inferInstance

namespace HasFiniteIrreducibleComponentsOnCompactOpens

/-- Let `S` be a scheme and let `X` be an algebraic space over `S`. The
following are equivalent: there is a surjective étale morphism `U ⟶ X` from a scheme such
that every quasi-compact open of `U` has finitely many irreducible components; for every
scheme `U` and every étale morphism `U ⟶ X` every quasi-compact open of `U` has finitely
many irreducible components; for every quasi-compact algebraic space `Y` étale over `X` the
set of codimension-`0` points of `Y` is finite; and for every quasi-compact algebraic space
`Y` étale over `X` the space `Points Y` has finitely many irreducible components. -/
theorem tfae {S : Scheme.{u}} (X : AlgebraicSpace S) :
    List.TFAE
      [existsSurjectiveEtale
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        forallEtale
          (fun U : Scheme.{u} ↦ Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U) X,
        finiteCodimZeroOnEtaleCompact X,
        finiteIrreducibleComponentsOnEtaleCompact X] :=
  sorry

/-- If `X` is representable by a scheme `T` over `S`, then
`HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T)` if and only if every
quasi-compact open of `T.left` has finitely many irreducible components. -/
theorem ofOver_iff {S : Scheme.{u}} (T : Over S) :
    HasFiniteIrreducibleComponentsOnCompactOpens (ofOver T) ↔
      Scheme.HasFiniteIrreducibleComponentsOnCompactOpens T.left :=
  sorry

end HasFiniteIrreducibleComponentsOnCompactOpens

end AlgebraicGeometry.AlgebraicSpace
