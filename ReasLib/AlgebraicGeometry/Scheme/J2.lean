module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Topology.RegularLocus

/-!
# J-2 schemes

The J-2 condition requires regular loci to be open after arbitrary locally finite type
scheme morphisms to a locally Noetherian base.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is J-2 if it is locally Noetherian and every scheme locally of finite type over
`X` has open regular locus. -/
@[stacks 07R3]
class IsJ2 (X : Scheme.{u}) : Prop extends IsLocallyNoetherian X where
  /-- Every scheme locally of finite type over a J-2 scheme has open regular locus. -/
  regularLocus_isOpen_of_locallyOfFiniteType {Y : Scheme.{u}} (f : Y ⟶ X)
      [LocallyOfFiniteType f] : IsOpen (Reg(Y))

variable (X : Scheme.{u})

/-- A locally Noetherian scheme is J-2 exactly when every scheme locally of finite type over it
has open regular locus. -/
@[stacks 07R3]
theorem isJ2_iff_forall_regularLocus_isOpen_of_locallyOfFiniteType [IsLocallyNoetherian X] :
    IsJ2 X ↔
      ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X) [LocallyOfFiniteType f],
        IsOpen (Reg(Y)) :=
  ⟨fun h _ f ↦
      h.regularLocus_isOpen_of_locallyOfFiniteType f,
    fun h ↦
      { toIsLocallyNoetherian := inferInstance
        regularLocus_isOpen_of_locallyOfFiniteType := fun f ↦ h f }⟩

/-- A scheme locally of finite type over a J-2 scheme is J-2. -/
theorem isJ2_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsJ2 X] [LocallyOfFiniteType f] : IsJ2 Y := sorry

/-- Every open subscheme of a J-2 scheme is J-2. -/
instance instIsJ2ToScheme {X : Scheme.{u}} [IsJ2 X] (U : X.Opens) : IsJ2 U.toScheme := by
  simpa using isJ2_of_locallyOfFiniteType U.ι

namespace IsJ2

/-- The regular locus of a J-2 scheme is open. -/
@[stacks 07R3]
theorem regularLocus_isOpen (X : Scheme.{u}) [IsJ2 X] :
    IsOpen (Reg(X)) := by
  let hX : IsJ2 X := inferInstance
  simpa using hX.regularLocus_isOpen_of_locallyOfFiniteType
    (CategoryTheory.CategoryStruct.id X)

end IsJ2

end AlgebraicGeometry.Scheme
