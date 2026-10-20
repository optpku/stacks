module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Essential-finiteness properties of directed approximations

The essential-finite-type assumptions used in local approximation arguments
are a property layer over `Hom`, not part of the primitive directed-system
data.  Keeping them here makes the condition reusable with locality,
flatness, or other independent property bundles.
-/

@[expose] public section

universe u v w

namespace Ring.DirectLimit.Algebra.Approximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace Hom

variable {f : R →+* S}

/-- Essential-finite-type conditions for a directed ring-hom approximation.

The source condition is taken over `ℤ`, while the stage-map condition is
relative to the source stage, matching the usual approximation data. -/
@[stacks 00R0 "essential-finite-type approximation"]
class EssFiniteType (A : Hom f) : Prop where
  /-- Every source stage is essentially of finite type over `ℤ`. -/
  source (i : A.index) :
    (Int.castRingHom (A.source i)).EssFiniteType
  /-- Every stage map is essentially of finite type over its source stage. -/
  map (i : A.index) : (A.map i).EssFiniteType

namespace EssFiniteType

/-- The stagewise specification of essential finite type, grouped by stage so
downstream constructions can unpack both conditions at once. -/
@[stacks 00R0 "essential-finite-type approximation"]
theorem spec (A : Hom f) [A.EssFiniteType] :
    ∀ i : A.index,
      (Int.castRingHom (A.source i)).EssFiniteType ∧
        (A.map i).EssFiniteType := sorry

end EssFiniteType

end Hom

namespace FiniteType

variable {f : R →+* S}

/-- A finite-type approximation carries the corresponding
essential-finite-type property bundle on its underlying approximation. -/
@[stacks 00R0 "essential-finite-type approximation"]
instance essFiniteType (A : FiniteType f) : A.toHom.EssFiniteType := sorry

end FiniteType

end Ring.DirectLimit.Algebra.Approximation
