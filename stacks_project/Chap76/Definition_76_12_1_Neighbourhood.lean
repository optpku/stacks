module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import stacks_project.Chap67.Definition_67_14_4_Subscheme
public import stacks_project.Chap67.Lemma_67_13_3
public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap67.Lemma_67_16_3_SchemeTheoreticImage
public import stacks_project.Chap67.Lemma_67_28_12_IdealSheaf
public import stacks_project.Chap67.Remark_67_12_4_Coborder
public import stacks_project.Chap76.Definition_76_6_5_Conormal
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood

/-!
# Infinitesimal neighbourhoods of immersions of algebraic spaces

The ideal-power construction and its canonical maps are provided by the shared
mathematical owner. The inclusion abbreviation preserves the existing spelling
for nested closed subspaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

#check (vanishes_of_le : ∀ {X Y : AlgebraicSpace S} {I J : IdealSubobject X},
  I ≤ J → ∀ {f : Y ⟶ X}, vanishes f J → vanishes f I)

/-- The closed-subspace inclusion induced by an inclusion of quasi-coherent
ideal sheaves, using the canonical inclusion. -/
abbrev subschemeInclusion {X : AlgebraicSpace S} {I J : IdealSubobject X}
    [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J) :
    subscheme J ⟶ subscheme I :=
  inclusion h

#check (inclusion_subschemeι : ∀ {X : AlgebraicSpace S} {I J : IdealSubobject X}
  [IsQuasiCoherent I] [IsQuasiCoherent J] (h : I ≤ J),
    inclusion h ≫ subschemeι I = subschemeι J)

namespace Hom.InfinitesimalNeighbourhood

variable {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsImmersion i]

#check (ideal i : ∀ (n : ℕ),
    IdealSubobject (IsImmersion.coborderRange i).X)

#check (ideal_eq_pow i : ∀ (n : ℕ),
    ideal i n = (idealSheafSubobject (IsImmersion.liftCoborder i)).pow (n + 1))

#check (ideal_le_idealSheafSubobject i : ∀ (n : ℕ),
    ideal i n ≤ idealSheafSubobject (IsImmersion.liftCoborder i))

#check (sections_pow_le i : ∀ (n : ℕ) (U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ),
    IdealSheaf.sections
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          U ^ (n + 1) ≤
      IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U)

#check (ideal_apply i : ∀ (n : ℕ) (U : (smallEtaleSite (IsImmersion.coborderRange i).X)ᵒᵖ)
    [AlgebraicGeometry.IsAffine ((smallEtaleToScheme (IsImmersion.coborderRange i).X).obj U.unop)],
    IdealSheaf.sections (Modules.toCommSubobject (ideal i n)) U =
      IdealSheaf.sections
          (Modules.toCommSubobject (idealSheafSubobject (IsImmersion.liftCoborder i)))
          U ^ (n + 1))

#check (space i : ∀ (n : ℕ),
    AlgebraicSpace S)

#check (space_eq_subscheme i : ∀ (n : ℕ),
    space i n = subscheme (ideal i n))

#check (toAmbient i : ∀ (n : ℕ),
    space i n ⟶ X)

#check (fromSource i : ∀ (n : ℕ),
    Z ⟶ space i n)

#check (fromSource_subschemeι i : ∀ (n : ℕ),
    fromSource i n ≫ subschemeι (ideal i n) = IsImmersion.liftCoborder i)

#check (fromSource_toAmbient i : ∀ (n : ℕ),
    fromSource i n ≫ toAmbient i n = i)

#check (fromSource_isClosedImmersion i : ∀ (n : ℕ),
    IsClosedImmersion (fromSource i n))

#check (toAmbient_isImmersion i : ∀ (n : ℕ),
    IsImmersion (toAmbient i n))

#check (fromSource_isNthOrderThickening i : ∀ (n : ℕ),
    IsNthOrderThickening n (fromSource i n))

#check (fromSource_isFirstOrderThickening i : IsFirstOrderThickening (fromSource i 1))

end Hom.InfinitesimalNeighbourhood

end AlgebraicGeometry.AlgebraicSpace
