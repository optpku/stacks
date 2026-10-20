module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.NoetherianSpace
public import ReasLib.RingTheory.CohenMacaulay.Module
import StacksCheckRecall

@[expose] public section

universe u v

section
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (M : Type v) [AddCommGroup M] [Module A M]

/- Exercise 111.62.1 (Definitions) (5): a Cohen-Macaulay module over a Noetherian local ring
`(A, m, κ)`. -/
@[stacks 0FWK] #check (Module.CohenMacaulay A M : Prop)

/- Clause 5: the support dimension and depth fields of a Cohen-Macaulay module. -/
#check (Module.supportDim A M)

#check (moduleDepth A M)

#check Module.CohenMacaulay.supportDim_eq_moduleDepth

end

section
variable {X : Type u} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] (s : Set X)

/- Clause 1: a constructible subset of a Noetherian topological space. -/
#check (Topology.IsConstructible s : Prop)

#check (IsLocallyClosed s : Prop)

#check (TopologicalSpace.NoetherianSpace.isCompact s)

end

section
variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
variable (M : Type v) [AddCommGroup M] [Module R M]

/- Clause 2: the localization of an `R`-module `M` at a prime `p`. -/
#check (LocalizedModule.AtPrime p M : Type (max u v))

#check IsLocalizedModule.AtPrime

#check LocalizedModule.mk

#check LocalizedModule.mkLinearMap

end

section
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
variable (M : Type v) [AddCommGroup M] [Module A M]

/- Clause 3: the length of a module over a Noetherian local ring
`(A, m, κ)`. -/
#check (Module.length A M : ℕ∞)

#check Module.length_eq_height

#check Module.length_ne_top_iff

#check (IsLocalRing.maximalIdeal A)

#check (IsLocalRing.ResidueField A)

end

section
variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/- Clause 4: a projective module over a ring `R`. -/
#check (Module.Projective R M : Prop)

#check Module.projective_lifting_property

#check Module.Projective.of_lifting_property

end
