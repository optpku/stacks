module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Algebraic schemes over a field

This leaf owns the standard finite-type and locally-finite-type predicates for
schemes equipped with a structure morphism to the spectrum of a field.
-/

@[expose] public section

open scoped AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k]

/-- A scheme over the field `k` is algebraic if its structure morphism to
`Spec (CommRingCat.of k)` is of finite type. -/
@[stacks 06LG]
abbrev Algebraic (X : Over (Spec (CommRingCat.of k))) : Prop :=
  Scheme.Hom.FiniteType X.hom

/-- A scheme of finite type over a field is Noetherian. -/
instance Algebraic.isNoetherian (X : Over (Spec (CommRingCat.of k))) [Algebraic X] :
    IsNoetherian X.left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom

/-- A finite-type morphism to `Spec k` defines an algebraic scheme over `k`.

This is an explicit bridge rather than a global instance, so a downstream declaration can choose
when it wants to expose the stronger bundled predicate. -/
theorem Algebraic.ofFiniteType
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Scheme.Hom.FiniteType f] :
    Algebraic (Over.mk f) := sorry

/-- A scheme over the field `k` is locally algebraic if its structure morphism to
`Spec (CommRingCat.of k)` is locally of finite type. -/
@[stacks 06LG]
abbrev LocallyAlgebraic (X : Over (Spec (CommRingCat.of k))) : Prop :=
  LocallyOfFiniteType X.hom

/-- Unfold `Algebraic X` into the canonical finite-type condition on the structure morphism. -/
@[stacks 06LG]
theorem algebraic_iff_finiteType (X : Over (Spec (CommRingCat.of k))) :
    Algebraic X ↔ Scheme.Hom.FiniteType X.hom := sorry

/-- Unfold `LocallyAlgebraic X` into the canonical locally-finite-type condition on the
structure morphism. -/
@[stacks 06LG]
theorem locallyAlgebraic_iff_locallyOfFiniteType (X : Over (Spec (CommRingCat.of k))) :
    LocallyAlgebraic X ↔ LocallyOfFiniteType X.hom := sorry

/-- Unfold `Algebraic X` as quasi-compactness together with local algebraicity of the structure
morphism. -/
@[stacks 06LG]
theorem algebraic_iff_quasiCompact_and_locallyAlgebraic (X : Over (Spec (CommRingCat.of k))) :
    Algebraic X ↔ QuasiCompact X.hom ∧ LocallyAlgebraic X := sorry

end

end AlgebraicGeometry
