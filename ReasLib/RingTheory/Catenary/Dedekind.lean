module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import ReasLib.RingTheory.Catenary.Universally

/-!
# Universal catenarity of Dedekind domains
-/

@[expose] public section

universe u v

namespace UniversallyCatenaryRing

/-- Every Dedekind domain is universally catenary. -/
@[stacks 00NM "Dedekind specialization"]
instance dedekind (R : Type u) [CommRing R] [IsDedekindDomain R] :
    UniversallyCatenaryRing.{u, v} R := sorry

end UniversallyCatenaryRing
