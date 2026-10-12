/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.Sets.Closeds

/-!
# Prime divisors

A prime divisor on a scheme is an integral closed subscheme of codimension one.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

section

variable (X : Scheme.{u})

/-- A prime divisor on a scheme is an integral closed subscheme whose irreducible closed support
has codimension one. -/
noncomputable def PrimeDivisor : Type u :=
  { I : { I : X.IdealSheafData //
      IsIntegral I.subscheme ∧ IsIrreducible (I.support : Set X) } //
    Order.coheight
      (⟨(I.1.support : Set X), I.2.2, I.1.support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds X) = 1 }

/-- Construct a prime divisor from an ideal sheaf defining an integral subscheme with irreducible
support of codimension one. -/
noncomputable def PrimeDivisor.ofIdeal (I : X.IdealSheafData)
    (h_integral : IsIntegral I.subscheme)
    (h_irreducible : IsIrreducible (I.support : Set X))
    (h_coheight : Order.coheight
      (⟨(I.support : Set X), h_irreducible, I.support.isClosed⟩ :
        TopologicalSpace.IrreducibleCloseds X) = 1) : PrimeDivisor X :=
  ⟨⟨I, h_integral, h_irreducible⟩, h_coheight⟩

/-- The ideal sheaf defining a prime divisor. -/
abbrev PrimeDivisor.ideal (Z : PrimeDivisor X) : X.IdealSheafData :=
  Z.1.1

/-- The integral closed subscheme underlying a prime divisor. -/
noncomputable abbrev PrimeDivisor.carrier (Z : PrimeDivisor X) : Scheme.{u} :=
  Z.ideal.subscheme

/-- The inclusion of the closed subscheme underlying a prime divisor. -/
noncomputable abbrev PrimeDivisor.ι (Z : PrimeDivisor X) : Z.carrier ⟶ X :=
  Z.ideal.subschemeι

/-- The inclusion of the closed subscheme underlying a prime divisor is a closed immersion. -/
theorem PrimeDivisor.isClosedImmersion_ι (Z : PrimeDivisor X) :
    IsClosedImmersion Z.ι :=
  inferInstance

/-- The closed subscheme underlying a prime divisor is integral. -/
theorem PrimeDivisor.isIntegral_carrier (Z : PrimeDivisor X) : IsIntegral Z.carrier :=
  Z.1.2.1

/-- The irreducible closed support underlying a prime divisor. -/
abbrev PrimeDivisor.support (Z : PrimeDivisor X) : TopologicalSpace.IrreducibleCloseds X :=
  ⟨(Z.ideal.support : Set X), Z.1.2.2, Z.ideal.support.isClosed⟩

/-- The support of a prime divisor is the image of its closed-immersion inclusion. -/
theorem PrimeDivisor.support_eq_range (Z : PrimeDivisor X) :
    (Z.support : Set X) = Set.range Z.ι.base :=
  Z.ideal.range_subschemeι.symm

/-- The underlying irreducible closed subset of a prime divisor has codimension `1`. -/
theorem PrimeDivisor.coheight_eq_one (Z : PrimeDivisor X) :
    Order.coheight Z.support = 1 :=
  Z.2

/-- The generic point of the support of a prime divisor. -/
noncomputable abbrev PrimeDivisor.genericPoint (Z : PrimeDivisor X) : X :=
    Z.support.isIrreducible.genericPoint


end

end AlgebraicGeometry
