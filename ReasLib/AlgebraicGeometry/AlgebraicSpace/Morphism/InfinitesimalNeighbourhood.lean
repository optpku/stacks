/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Inclusion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Coborder
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeTheoreticImage.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Power
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FiniteOrder

/-!
# Infinitesimal neighbourhoods of immersions of algebraic spaces

The `n`th infinitesimal neighbourhood of an immersion `i : Z ⟶ X` is the closed
subspace of the coborder open cut out by the `(n + 1)`st power of the coborder
kernel ideal. The canonical maps `Z ⟶ Z_n ⟶ X` realize this as an `n`th-order
thickening of `Z` over `X`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace Hom.InfinitesimalNeighbourhood

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

/-- The ideal defining the `n`th infinitesimal neighbourhood is the
`(n + 1)`st power of the kernel ideal on the coborder open. -/
@[reducible]
def ideal (n : ℕ) : IdealSubobject (IsImmersion.coborderRange i).X :=
  (idealSheafSubobject (IsImmersion.liftCoborder i)).pow (n + 1)

/-- The neighbourhood ideal is the corresponding power of the coborder
kernel ideal. -/
theorem ideal_eq_pow (n : ℕ) :
    ideal i n = (idealSheafSubobject (IsImmersion.liftCoborder i)).pow (n + 1) :=
  rfl

/-- The defining ideal of the `n`th infinitesimal neighbourhood is contained in
the coborder kernel ideal. -/
theorem ideal_le_idealSheafSubobject (n : ℕ) :
    ideal i n ≤ idealSheafSubobject (IsImmersion.liftCoborder i) :=
  sorry

/-- Ordinary section powers of the coborder kernel lie in the sheaf-image
sections of the neighbourhood ideal. -/
theorem sections_pow_le (n : ℕ) (U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ) :
    IdealSheaf.sections
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          U ^ (n + 1) ≤
      IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U :=
  sorry

/-- On affine étale objects, the defining ideal of the `n`th infinitesimal
neighbourhood is the `(n + 1)`st power of the coborder kernel ideal. -/
theorem ideal_apply (n : ℕ) (U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ)
    [AlgebraicGeometry.IsAffine ((smallEtaleToScheme (IsImmersion.coborderRange i).X).obj U.unop)] :
    IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U =
      IdealSheaf.sections
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          U ^ (n + 1) :=
  sorry

/-- The `n`th infinitesimal neighbourhood of the source of an immersion, as a
closed subspace of the coborder open. -/
def space (n : ℕ) : AlgebraicSpace S :=
  subscheme (ideal i n)

/-- The infinitesimal-neighbourhood space is the closed subspace cut out by the
corresponding power of the coborder kernel ideal. -/
theorem space_eq_subscheme (n : ℕ) :
    space i n = subscheme (ideal i n) :=
  rfl

/-- The canonical morphism from an infinitesimal neighbourhood to the ambient
algebraic space. -/
def toAmbient (n : ℕ) : space i n ⟶ X :=
  subschemeι (ideal i n) ≫ (IsImmersion.coborderRange i).ι

/-- The canonical morphism from the source of an immersion to its `n`th
infinitesimal neighbourhood. -/
def fromSource (n : ℕ) : Z ⟶ space i n :=
  toIdealImage (IsImmersion.liftCoborder i) ≫
    inclusion (ideal_le_idealSheafSubobject i n)

/-- The source morphism followed by the closed-subspace inclusion recovers the
coborder closed factor of the immersion. -/
theorem fromSource_subschemeι (n : ℕ) :
    fromSource i n ≫ subschemeι (ideal i n) = IsImmersion.liftCoborder i :=
  sorry

/-- The infinitesimal-neighbourhood factorization recovers the original
immersion. -/
theorem fromSource_toAmbient (n : ℕ) :
    fromSource i n ≫ toAmbient i n = i :=
  sorry

/-- The canonical map from the source to its infinitesimal neighbourhood is a
closed immersion. -/
instance fromSource_isClosedImmersion (n : ℕ) :
    IsClosedImmersion (fromSource i n) :=
  sorry

/-- The canonical map from an infinitesimal neighbourhood to the ambient space
is an immersion. -/
instance toAmbient_isImmersion (n : ℕ) : IsImmersion (toAmbient i n) :=
  sorry

/-- The canonical map from an immersion to its `n`th infinitesimal neighbourhood
is an `n`th-order thickening. -/
instance fromSource_isNthOrderThickening (n : ℕ) :
    IsNthOrderThickening n (fromSource i n) :=
  sorry

/-- The canonical map from an immersion to its first-order infinitesimal
neighbourhood is a first-order thickening. -/
instance fromSource_isFirstOrderThickening :
    IsFirstOrderThickening (fromSource i 1) :=
  IsNthOrderThickening.instIsFirstOrderThickening (fromSource i 1)

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
