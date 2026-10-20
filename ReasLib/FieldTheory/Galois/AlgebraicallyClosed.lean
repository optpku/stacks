module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

universe u

namespace Field

/-- The absolute Galois group of an algebraically closed field is trivial. -/
instance absoluteGaloisGroup_subsingleton (K : Type u) [Field K] [IsAlgClosed K] :
    Subsingleton (absoluteGaloisGroup K) := sorry

end Field
