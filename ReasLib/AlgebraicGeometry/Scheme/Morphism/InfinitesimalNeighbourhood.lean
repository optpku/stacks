module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-- The power of the ideal sheaf defining the canonical closed factor of an immersion that
defines its `n`th infinitesimal neighbourhood. -/
def ideal (n : ℕ) : i.coborderRange.toScheme.IdealSheafData :=
  i.liftCoborder.ker ^ (n + 1)

/-- The ideal defining an infinitesimal neighbourhood is pointwise the corresponding power
of the ideal of the canonical closed factor. -/
theorem ideal_apply (n : ℕ) (U : i.coborderRange.toScheme.affineOpens) :
    (ideal i n).ideal U = (i.liftCoborder.ker.ideal U) ^ (n + 1) := sorry

/-- The `n`th infinitesimal neighbourhood of the source of an immersion inside its canonical
open coborder. -/
def scheme (n : ℕ) : Scheme.{u} :=
  (ideal i n).subscheme

/-- The infinitesimal-neighbourhood scheme is the subscheme defined by the corresponding
power of the immersion ideal. -/
theorem scheme_eq_subscheme (n : ℕ) :
    scheme i n = (ideal i n).subscheme := sorry

/-- The canonical morphism from an infinitesimal neighbourhood to the ambient scheme. -/
def toAmbient (n : ℕ) : scheme i n ⟶ X :=
  (ideal i n).subschemeι ≫ i.coborderRange.ι

/-- The canonical morphism from the source of an immersion to its `n`th infinitesimal
neighbourhood. -/
def fromSource (n : ℕ) : Z ⟶ scheme i n :=
  i.liftCoborder.toImage ≫ Scheme.IdealSheafData.inclusion
    (fun _ ↦ Ideal.pow_le_self (Nat.succ_ne_zero n))

/-- The source morphism followed by the closed-subscheme inclusion recovers the canonical
closed factor of the immersion. -/
theorem fromSource_subschemeι (n : ℕ) :
    fromSource i n ≫ (ideal i n).subschemeι = i.liftCoborder := sorry

/-- The infinitesimal-neighbourhood factorization recovers the original immersion. -/
theorem fromSource_toAmbient (n : ℕ) :
    fromSource i n ≫ toAmbient i n = i := sorry

/-- The canonical map from the source to its infinitesimal neighbourhood is a closed
immersion. -/
instance fromSource_isClosedImmersion (n : ℕ) : IsClosedImmersion (fromSource i n) := sorry

/-- The canonical map from an infinitesimal neighbourhood to the ambient scheme is an
immersion. -/
instance toAmbient_isImmersion (n : ℕ) : IsImmersion (toAmbient i n) := sorry

/-- The source and its infinitesimal neighbourhood have the same underlying topological
space. -/
theorem surjective_fromSource (n : ℕ) : Function.Surjective (fromSource i n) := sorry

/-- The kernel of the source map to its `n`th infinitesimal neighbourhood has vanishing
`(n + 1)`st power. -/
theorem ker_fromSource_pow_succ (n : ℕ) :
    (fromSource i n).ker ^ (n + 1) = ⊥ := sorry

/-- The canonical map from an immersion to its `n`th infinitesimal neighbourhood is an
`n`th-order thickening. -/
instance fromSource_isNthOrderThickening (n : ℕ) :
    IsNthOrderThickening n (fromSource i n) := sorry

end AlgebraicGeometry.Scheme.Hom.InfinitesimalNeighbourhood
