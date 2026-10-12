/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DescentDatum.Canonical

/-!
# Effective module descent data

This file defines isomorphisms of concrete module descent data and the predicate
that a datum is induced, up to isomorphism, by scalar extension.
-/

@[expose] public section

noncomputable section

open ModuleCat
open scoped TensorProduct.Right

namespace Module.DescentDatum

universe u

variable {R A N N' : Type u}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N] [SMulCommClass R A N]
variable [AddCommGroup N'] [Module R N'] [Module A N']
variable [IsScalarTower R A N'] [SMulCommClass R A N']

/-- An isomorphism of concrete module descent data consists of mutually
inverse morphisms of descent data. -/
structure Iso (D : DescentDatum R A N) (D' : DescentDatum R A N') where
  /-- The forward morphism of descent data. -/
  hom : Hom D D'
  /-- The inverse morphism of descent data. -/
  inv : Hom D' D
  /-- The forward morphism followed by the inverse is the identity. -/
  hom_inv_id : Hom.comp hom inv = Hom.id D
  /-- The inverse followed by the forward morphism is the identity. -/
  inv_hom_id : Hom.comp inv hom = Hom.id D'

namespace Iso

/-- Every concrete module descent datum is isomorphic to itself. -/
def refl (D : DescentDatum R A N) : Iso D D where
  hom := Hom.id D
  inv := Hom.id D
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of the reflexive isomorphism is the identity. -/
theorem refl_hom (D : DescentDatum R A N) : (refl D).hom = Hom.id D := sorry

end Iso

/-- A concrete module descent datum is effective when it is isomorphic to
the canonical datum on the scalar extension of some `R`-module. -/
def IsEffective (D : DescentDatum R A N) : Prop :=
  ∃ M : ModuleCat.{u} R, Nonempty (Iso (canonical R A M) D)

/-- Effectiveness is exactly the existence of an `R`-module whose canonical
scalar-extension descent datum is isomorphic to the given datum. -/
theorem isEffective_iff (D : DescentDatum R A N) :
    IsEffective D ↔ ∃ M : ModuleCat.{u} R, Nonempty (Iso (canonical R A M) D) := sorry

namespace IsEffective

/-- The canonical descent datum of an `R`-module is effective. -/
theorem of_canonical (M : ModuleCat.{u} R) : IsEffective (canonical R A M) := sorry

end IsEffective

end Module.DescentDatum
