module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.RelativeCycle.Operations

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- Over a locally Noetherian base, a family of fibrewise `r`-cycles on a scheme
locally of finite type is relative if and only if its pushforward along a closed
immersion into another scheme locally of finite type over the base is relative. -/
theorem isRelative_iff_pushforward {X Y S : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fY]
    (i : X ⟶ Y) [IsClosedImmersion i] (hc : i ≫ fY = fX) (r : ℕ)
    (α : fX.FiberCycleFamily r) :
    IsRelative α ↔ IsRelative (pushforward fY i hc α) := sorry

/-- The closed-immersion pushforward of a relative `r`-cycle over a locally
Noetherian base is a relative `r`-cycle. -/
theorem groupPushforward_mem {X X' S : Scheme.{u}} (fX : X ⟶ S) (fX' : X' ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType fX] [LocallyOfFiniteType fX']
    (i : X ⟶ X') [IsClosedImmersion i] (hc : i ≫ fX' = fX) (r : ℕ)
    (α : group fX r) :
    pushforward fX' i hc (α : fX.FiberCycleFamily r) ∈ group fX' r :=
  (isRelative_iff_pushforward fX fX' i hc r (α : fX.FiberCycleFamily r)).mp α.property

/-- Pushforward of relative `r`-cycles along a closed immersion over a locally
Noetherian base, as an additive homomorphism. -/
noncomputable def groupPushforward {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) : group fX r →+ group fX' r :=
  ((AddMonoidHom.pi fun s : S ↦
    (CycleGroup.mapHom (pushforwardFiberMap fX fX' i hc s)
      (fX.fiberDimensionFunction s) (fX'.fiberDimensionFunction s) r).comp
        (Pi.evalAddMonoidHom
          (fun t : S ↦ CycleGroup (fX.fiber t) (fX.fiberDimensionFunction t) r) s)).comp
    (group fX r).subtype).codRestrict (group fX' r)
      (groupPushforward_mem fX fX' i hc r)

/-- The underlying fibrewise family of the relative-cycle pushforward is the
family-level pushforward. -/
theorem groupPushforward_apply {X X' S : Scheme.{u}} (fX : X ⟶ S)
    (fX' : X' ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType fX]
    [LocallyOfFiniteType fX'] (i : X ⟶ X') [IsClosedImmersion i]
    (hc : i ≫ fX' = fX) (r : ℕ) (α : group fX r) :
    (groupPushforward fX fX' i hc r α : fX'.FiberCycleFamily r) =
      pushforward fX' i hc (α : fX.FiberCycleFamily r) := rfl

end AlgebraicGeometry.RelativeCycle
