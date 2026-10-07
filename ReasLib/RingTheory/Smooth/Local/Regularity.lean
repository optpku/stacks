module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regularity of formally smooth local algebras

This leaf records the local regularity consequence of formal smoothness at
the essentially finite-type level.
-/

@[expose] public section

universe u v

namespace Algebra.FormallySmooth

/-- An essentially finite-type formally smooth local algebra over a field is regular. -/
@[stacks 00TT "regularity of formally smooth local algebras over fields"]
theorem isRegularLocalRing
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra.EssFiniteType k A] [Algebra.FormallySmooth k A] :
    IsRegularLocalRing A := sorry

end Algebra.FormallySmooth
