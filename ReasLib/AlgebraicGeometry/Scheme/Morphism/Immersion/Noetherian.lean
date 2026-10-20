module

public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- An immersion into a locally Noetherian scheme is quasi-compact. -/
instance (priority := 100) quasiCompact_of_isImmersion_of_isLocallyNoetherian
    {Z X : Scheme.{u}} {f : Z ⟶ X} [IsImmersion f] [IsLocallyNoetherian X] :
    QuasiCompact f := by
  rw [← f.liftCoborder_ι]
  infer_instance

/-- The source of an immersion into a locally Noetherian scheme is locally Noetherian. -/
theorem IsLocallyNoetherian.of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsLocallyNoetherian Y] :
    IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

/-- The source of an immersion into a Noetherian scheme is Noetherian. -/
theorem IsNoetherian.of_isImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsNoetherian Y] :
    IsNoetherian X := sorry

end AlgebraicGeometry
