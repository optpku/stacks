/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Six-term homology sequences from mapping cocones

A comparison `c : L ⟶ mappingCocone f` whose degree-zero homology map is invertible
transports the central six-term segment of the long exact homology sequence of
`mappingCocone.triangle f`.  Exactness only additionally requires the degree `-1` homology map
of `c` to be epic.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open HomologicalComplex

noncomputable section

universe v u

namespace CochainComplex.mappingCocone

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace SixTerm

/-- The map from degree `-1` homology of the comparison source to degree `-1` homology of the
source complex. -/
@[stacks 0E1Y "first map", stacks 0E1Z "first map"]
noncomputable def leftNegOne
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y) (c : L ⟶ mappingCocone f) :
    homology L (-1) ⟶ homology X (-1) :=
  homologyMap (c ≫ fst f) (-1)

/-- The degree `-1` homology map of the original cochain map. -/
@[stacks 0E1Y "second map", stacks 0E1Z "second map"]
noncomputable def mapNegOne
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    homology X (-1) ⟶ homology Y (-1) :=
  homologyMap f (-1)

/-- The connecting map from degree `-1` homology of the target to degree `0` homology of the
comparison source. -/
@[stacks 0E1Y "connecting map", stacks 0E1Z "connecting map"]
noncomputable def boundary
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    homology Y (-1) ⟶ homology L 0 :=
  homologyδOfTriangle (triangle f) (-1) 0 ≫
    @inv _ _ _ _ (homologyMap c 0) hc0

/-- The map from degree `0` homology of the comparison source to degree `0` homology of the
source complex. -/
@[stacks 0E1Y "fourth map", stacks 0E1Z "fourth map"]
noncomputable def leftZero
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y) (c : L ⟶ mappingCocone f) :
    homology L 0 ⟶ homology X 0 :=
  homologyMap (c ≫ fst f) 0

/-- The degree `0` homology map of the original cochain map. -/
@[stacks 0E1Y "fifth map", stacks 0E1Z "fifth map"]
noncomputable def mapZero
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    homology X 0 ⟶ homology Y 0 :=
  homologyMap f 0

end SixTerm

/-- The six-term homology segment transported along
`c : L ⟶ mappingCocone f` in degrees `-1` and `0`.

The explicit proof `hc0` selects the inverse of `homologyMap c 0` without changing the local
instance environment. -/
@[stacks 0E1Y "mapping-cocone six-term sequence",
  stacks 0E1Z "mapping-cocone six-term sequence"]
noncomputable def sixTerm
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    ComposableArrows C 5 :=
  mk₅
    (SixTerm.leftNegOne f c)
    (SixTerm.mapNegOne f)
    (SixTerm.boundary f c hc0)
    (SixTerm.leftZero f c)
    (SixTerm.mapZero f)

/-- The first arrow of `sixTerm` is `SixTerm.leftNegOne`. -/
theorem sixTerm_map_zero_one
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    (sixTerm f c hc0).map' 0 1 = SixTerm.leftNegOne f c := sorry

/-- The second arrow of `sixTerm` is the degree `-1` homology map of `f`. -/
theorem sixTerm_map_one_two
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    (sixTerm f c hc0).map' 1 2 = SixTerm.mapNegOne f := sorry

/-- The third arrow of `sixTerm` is its connecting morphism. -/
theorem sixTerm_map_two_three
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    (sixTerm f c hc0).map' 2 3 = SixTerm.boundary f c hc0 := sorry

/-- The fourth arrow of `sixTerm` is `SixTerm.leftZero`. -/
theorem sixTerm_map_three_four
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    (sixTerm f c hc0).map' 3 4 = SixTerm.leftZero f c := sorry

/-- The fifth arrow of `sixTerm` is the degree `0` homology map of `f`. -/
theorem sixTerm_map_four_five
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0)) :
    (sixTerm f c hc0).map' 4 5 = SixTerm.mapZero f := sorry

/-- The transported six-term segment is exact when `homologyMap c (-1)` is epic. -/
@[stacks 0E1Y "exact mapping-cocone six-term sequence",
  stacks 0E1Z "exact mapping-cocone six-term sequence"]
theorem sixTerm_exact
    {L X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (c : L ⟶ mappingCocone f) (hc0 : IsIso (homologyMap c 0))
    [Epi (homologyMap c (-1))] :
    (sixTerm f c hc0).Exact := sorry

/-- The degree-zero homology map of `f` is epic when degree-one homology of its mapping cocone
vanishes. -/
@[stacks 0E1Y "final epimorphism in the six-term sequence",
  stacks 0E1Z "final epimorphism in the six-term sequence"]
theorem h0_epi
    {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (hH1 : IsZero (homology (mappingCocone f) 1)) :
    Epi (homologyMap f 0) := sorry

end CochainComplex.mappingCocone
