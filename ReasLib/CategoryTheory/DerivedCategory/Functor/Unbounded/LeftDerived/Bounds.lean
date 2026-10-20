/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.Acyclic.Left
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Homology
public import ReasLib.CategoryTheory.Triangulated.TStructure.Functor
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounds for Unbounded Left Derived Functors

This is the bounded-above dual of the right-derived bounds API.  It is stated for an arbitrary
realization of the left-derived universal property, while finite homological dimension is
measured by the canonical bounded-above derived degree.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Homotopy

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive]
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
    Functor.Homotopy.toDerived F)
  [hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ))]

include hLF

namespace TruncGE

/-- Stacks 07K8 (5): applying a left derived functor to lower truncation induces a
cohomology isomorphism throughout the retained range. -/
@[stacks 07K8]
theorem homologyMap_isIso
    (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((DerivedCategory.homologyFunctor B i).map
        (LF.map ((DerivedCategory.TStructure.t.truncGEπ b).app E))) := sorry

/-- The cohomology comparison obtained by applying a left derived functor to lower
truncation. -/
@[stacks 07K8]
noncomputable def homologyIso
    (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :=
  @asIso _ _ _ _
    ((DerivedCategory.homologyFunctor B i).map
      (LF.map ((DerivedCategory.TStructure.t.truncGEπ b).app E)))
    (homologyMap_isIso F LF ε E b i hi)

/-- The forward map of `homologyIso` is the mapped lower-truncation comparison. -/
@[simp]
theorem homologyIso_hom
    (E : DerivedCategory A) (b i : ℤ) (hi : b ≤ i) :
    (homologyIso F LF ε E b i hi).hom =
      (DerivedCategory.homologyFunctor B i).map
        (LF.map ((DerivedCategory.TStructure.t.truncGEπ b).app E)) := sorry

/-- The lower-truncation cohomology isomorphisms are natural in the derived object. -/
@[reassoc, stacks 07K8 "lower-truncation left-derived homology comparison naturality"]
theorem homologyIso_hom_naturality
    {E E' : DerivedCategory A} (f : E ⟶ E') (b i : ℤ) (hi : b ≤ i) :
    (DerivedCategory.homologyFunctor B i).map (LF.map f) ≫
        (homologyIso F LF ε E' b i hi).hom =
      (homologyIso F LF ε E b i hi).hom ≫
        (DerivedCategory.homologyFunctor B i).map
          (LF.map ((DerivedCategory.TStructure.t.truncGE b).map f)) := sorry

/-- The inverse lower-truncation cohomology comparisons are natural in the derived object. -/
@[reassoc, stacks 07K8 "inverse lower-truncation left-derived homology comparison naturality"]
theorem homologyIso_inv_naturality
    {E E' : DerivedCategory A} (f : E ⟶ E') (b i : ℤ) (hi : b ≤ i) :
    (homologyIso F LF ε E b i hi).inv ≫
        (DerivedCategory.homologyFunctor B i).map (LF.map f) =
      (DerivedCategory.homologyFunctor B i).map
          (LF.map ((DerivedCategory.TStructure.t.truncGE b).map f)) ≫
        (homologyIso F LF ε E' b i hi).inv := sorry

end TruncGE

/-- An unbounded left derived functor preserves every upper cohomological bound. -/
@[stacks 07K8]
theorem mapsLE :
    Functor.TStructure.MapsLE LF DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t 0 := sorry

end CategoryTheory.Functor.LeftDerived.Homotopy

namespace CategoryTheory.Functor.LeftAcyclic.Unbounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
  [(LeftAcyclic.Bounded F).HasEpiCover]
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
    Functor.Homotopy.toDerived F)
  [hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ))]

include hLF

namespace Vanishes

namespace TruncLE

/-- Stacks 07K8 (4): if the bounded-above left derived functor vanishes in degree `n`,
truncating above `a + n - 1` does not change left-derived cohomology in degrees at most `a`. -/
@[stacks 07K8]
theorem homologyMap_isIso
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    IsIso
      ((DerivedCategory.homologyFunctor B i).map
        (LF.map
          ((DerivedCategory.TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E))) := sorry

/-- The cohomology comparison obtained from upper truncation under finite left-derived
dimension. -/
@[stacks 07K8]
noncomputable def homologyIso
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :=
  @asIso _ _ _ _
    ((DerivedCategory.homologyFunctor B i).map
      (LF.map
        ((DerivedCategory.TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E)))
    (homologyMap_isIso F LF ε n h_n E a i hi)

/-- The forward map of `homologyIso` is the mapped upper-truncation comparison. -/
@[simp]
theorem homologyIso_hom
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    (E : DerivedCategory A) (a i : ℤ) (hi : i ≤ a) :
    (homologyIso F LF ε n h_n E a i hi).hom =
      (DerivedCategory.homologyFunctor B i).map
        (LF.map
          ((DerivedCategory.TStructure.t.truncLEι (a + (n : ℤ) - 1)).app E)) := sorry

/-- The finite-dimensional upper-truncation cohomology isomorphisms are natural in the
derived object. -/
@[reassoc, stacks 07K8 "finite-dimensional upper-truncation homology comparison naturality"]
theorem homologyIso_hom_naturality
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    {E E' : DerivedCategory A} (f : E ⟶ E') (a i : ℤ) (hi : i ≤ a) :
    (DerivedCategory.homologyFunctor B i).map
          (LF.map ((DerivedCategory.TStructure.t.truncLE
            (a + (n : ℤ) - 1)).map f)) ≫
        (homologyIso F LF ε n h_n E' a i hi).hom =
      (homologyIso F LF ε n h_n E a i hi).hom ≫
        (DerivedCategory.homologyFunctor B i).map (LF.map f) := sorry

/-- The inverse finite-dimensional upper-truncation cohomology comparisons are natural in the
derived object. -/
@[reassoc, stacks 07K8
  "inverse finite-dimensional upper-truncation homology comparison naturality"]
theorem homologyIso_inv_naturality
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    {E E' : DerivedCategory A} (f : E ⟶ E') (a i : ℤ) (hi : i ≤ a) :
    (homologyIso F LF ε n h_n E a i hi).inv ≫
        (DerivedCategory.homologyFunctor B i).map
          (LF.map ((DerivedCategory.TStructure.t.truncLE
            (a + (n : ℤ) - 1)).map f)) =
      (DerivedCategory.homologyFunctor B i).map (LF.map f) ≫
        (homologyIso F LF ε n h_n E' a i hi).inv := sorry

end TruncLE

/-- Finite left-derived dimension `n` shifts lower cohomological bounds by at most `1 - n`. -/
@[stacks 07K8]
theorem mapsGE
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n) :
    Functor.TStructure.MapsGE LF DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t (1 - (n : ℤ)) := sorry

/-- Finite left-derived dimension `n` gives cohomological amplitude `[1 - n, 0]`. -/
@[stacks 07K8]
theorem hasAmplitude
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n) :
    Functor.TStructure.HasAmplitude LF DerivedCategory.TStructure.t
      DerivedCategory.TStructure.t (1 - (n : ℤ)) 0 := sorry

end Vanishes

end CategoryTheory.Functor.LeftAcyclic.Unbounded
