module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.Acyclic.Right
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounds for Unbounded Right Derived Functors

The statements are formulated for any realization of the right-derived universal property.
The lower bound is intrinsic to right derivation; the upper bound uses finite cohomological
dimension expressed through the canonical bounded-below derived degree.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Homotopy

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (η : Functor.Homotopy.toDerived F ⟶
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ RF)
  [hRF : RF.IsRightDerivedFunctor η (HomotopyCategory.quasiIso A (up ℤ))]

include hRF

namespace TruncLE

/-- Stacks 07K7 (4a): applying a right derived functor to upper truncation induces a
cohomology isomorphism throughout the retained range. -/
@[stacks 07K7]
theorem homologyMap_isIso
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((DerivedCategory.homologyFunctor B i).map
        (RF.map ((DerivedCategory.TStructure.t.truncLEι a).app E))) := sorry

/-- The cohomology comparison obtained by applying a right derived functor to upper
truncation. -/
@[stacks 07K7]
noncomputable def homologyIso
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :=
  @asIso _ _ _ _
    ((DerivedCategory.homologyFunctor B i).map
      (RF.map ((DerivedCategory.TStructure.t.truncLEι a).app E)))
    (homologyMap_isIso F RF η E a i hi)

/-- The forward map of `homologyIso` is the mapped upper-truncation comparison. -/
@[simp]
theorem homologyIso_hom
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    (homologyIso F RF η E a i hi).hom =
      (DerivedCategory.homologyFunctor B i).map
        (RF.map ((DerivedCategory.TStructure.t.truncLEι a).app E)) := sorry

/-- The upper-truncation cohomology isomorphisms are natural in the derived object. -/
@[reassoc, stacks 07K7 "upper-truncation right-derived homology comparison naturality"]
theorem homologyIso_hom_naturality
    {E E' : DerivedCategory A} (f : E ⟶ E') (a i : ℤ) (hi : i ≤ a) :
    (DerivedCategory.homologyFunctor B i).map
          (RF.map ((DerivedCategory.TStructure.t.truncLE a).map f)) ≫
        (homologyIso F RF η E' a i hi).hom =
      (homologyIso F RF η E a i hi).hom ≫
        (DerivedCategory.homologyFunctor B i).map (RF.map f) := sorry

/-- The inverse upper-truncation cohomology comparisons are natural in the derived object. -/
@[reassoc, stacks 07K7 "inverse upper-truncation right-derived homology comparison naturality"]
theorem homologyIso_inv_naturality
    {E E' : DerivedCategory A} (f : E ⟶ E') (a i : ℤ) (hi : i ≤ a) :
    (homologyIso F RF η E a i hi).inv ≫
        (DerivedCategory.homologyFunctor B i).map
          (RF.map ((DerivedCategory.TStructure.t.truncLE a).map f)) =
      (DerivedCategory.homologyFunctor B i).map (RF.map f) ≫
        (homologyIso F RF η E' a i hi).inv := sorry

end TruncLE

/-- An unbounded right derived functor preserves every lower cohomological bound. -/
@[stacks 07K7]
theorem mapsGE :
    Functor.TStructure.MapsGE RF DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t 0 := sorry

end CategoryTheory.Functor.RightDerived.Homotopy

namespace CategoryTheory.Functor.RightAcyclic.Unbounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [(RightAcyclic.Bounded F).HasMonoEmbedding]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (η : Functor.Homotopy.toDerived F ⟶
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ RF)
  [hRF : RF.IsRightDerivedFunctor η (HomotopyCategory.quasiIso A (up ℤ))]

include hRF

namespace Vanishes

namespace TruncGE

/-- Stacks 07K7 (4b): if the bounded-below right derived functor vanishes in degree `n`,
truncating below `b - n + 1` does not change right-derived cohomology in degrees at least `b`. -/
@[stacks 07K7]
theorem homologyMap_isIso
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((DerivedCategory.homologyFunctor B i).map
        (RF.map
          ((DerivedCategory.TStructure.t.truncGEπ (b - (n : ℤ) + 1)).app E))) := sorry

/-- The cohomology comparison obtained from lower truncation under finite right-derived
dimension. -/
@[stacks 07K7]
noncomputable def homologyIso
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :=
  @asIso _ _ _ _
    ((DerivedCategory.homologyFunctor B i).map
      (RF.map
        ((DerivedCategory.TStructure.t.truncGEπ (b - (n : ℤ) + 1)).app E)))
    (homologyMap_isIso F RF η n h_n E b i hi)

/-- The forward map of `homologyIso` is the mapped lower-truncation comparison. -/
@[simp]
theorem homologyIso_hom
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :
    (homologyIso F RF η n h_n E b i hi).hom =
      (DerivedCategory.homologyFunctor B i).map
        (RF.map
          ((DerivedCategory.TStructure.t.truncGEπ (b - (n : ℤ) + 1)).app E)) := sorry

/-- The finite-dimensional lower-truncation cohomology isomorphisms are natural in the
derived object. -/
@[reassoc, stacks 07K7 "finite-dimensional lower-truncation homology comparison naturality"]
theorem homologyIso_hom_naturality
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    {E E' : DerivedCategory A} (f : E ⟶ E') (b i : ℤ) (hi : b ≤ i) :
    (DerivedCategory.homologyFunctor B i).map (RF.map f) ≫
        (homologyIso F RF η n h_n E' b i hi).hom =
      (homologyIso F RF η n h_n E b i hi).hom ≫
        (DerivedCategory.homologyFunctor B i).map
          (RF.map ((DerivedCategory.TStructure.t.truncGE
            (b - (n : ℤ) + 1)).map f)) := sorry

/-- The inverse finite-dimensional lower-truncation cohomology comparisons are natural in the
derived object. -/
@[reassoc, stacks 07K7
  "inverse finite-dimensional lower-truncation homology comparison naturality"]
theorem homologyIso_inv_naturality
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    {E E' : DerivedCategory A} (f : E ⟶ E') (b i : ℤ) (hi : b ≤ i) :
    (homologyIso F RF η n h_n E b i hi).inv ≫
        (DerivedCategory.homologyFunctor B i).map (RF.map f) =
      (DerivedCategory.homologyFunctor B i).map
          (RF.map ((DerivedCategory.TStructure.t.truncGE
            (b - (n : ℤ) + 1)).map f)) ≫
        (homologyIso F RF η n h_n E' b i hi).inv := sorry

end TruncGE

/-- Finite right-derived dimension `n` shifts upper cohomological bounds by at most `n - 1`. -/
@[stacks 07K7]
theorem mapsLE
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n) :
    Functor.TStructure.MapsLE RF DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t ((n : ℤ) - 1) := sorry

/-- Finite right-derived dimension `n` gives cohomological amplitude `[0, n - 1]`. -/
@[stacks 07K7]
theorem hasAmplitude
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n) :
    Functor.TStructure.HasAmplitude RF DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t 0 ((n : ℤ) - 1) := sorry

end Vanishes

end CategoryTheory.Functor.RightAcyclic.Unbounded
