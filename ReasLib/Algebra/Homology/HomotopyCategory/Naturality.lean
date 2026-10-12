/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Natural isomorphisms on homotopy categories

Mathlib provides the action of a natural transformation on homotopy categories.  This
file packages the action of a natural isomorphism, with explicit forward and inverse data,
so restrictions and localizations can reuse it without rebuilding the inverse laws.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂ u₃

namespace CategoryTheory.NatIso

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
  {ι : Type u₃}

/-- A natural isomorphism of additive functors induces a natural isomorphism on
homotopy categories. -/
@[stacks 014X "naturality of the induced homotopy-category functor"]
def mapHomotopyCategory {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (c : ComplexShape ι) :
    F.mapHomotopyCategory c ≅ G.mapHomotopyCategory c where
  hom := NatTrans.mapHomotopyCategory e.hom c
  inv := NatTrans.mapHomotopyCategory e.inv c
  hom_inv_id := sorry
  inv_hom_id := sorry

namespace mapHomotopyCategory

/-- The forward map of `NatIso.mapHomotopyCategory` is induced by the forward ambient
natural transformation. -/
@[simp]
theorem hom {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (c : ComplexShape ι) :
    (NatIso.mapHomotopyCategory e c).hom =
      NatTrans.mapHomotopyCategory e.hom c := sorry

/-- The inverse map of `NatIso.mapHomotopyCategory` is induced by the inverse ambient
natural transformation. -/
@[simp]
theorem inv {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (c : ComplexShape ι) :
    (NatIso.mapHomotopyCategory e c).inv =
      NatTrans.mapHomotopyCategory e.inv c := sorry

/-- The forward component of `NatIso.mapHomotopyCategory` is the corresponding component
of `NatTrans.mapHomotopyCategory`. -/
@[simp]
theorem hom_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    (NatIso.mapHomotopyCategory e c).hom.app
        ((HomotopyCategory.quotient C c).obj K) =
      (NatTrans.mapHomotopyCategory e.hom c).app
        ((HomotopyCategory.quotient C c).obj K) := sorry

/-- The inverse component of `NatIso.mapHomotopyCategory` is the corresponding component
of `NatTrans.mapHomotopyCategory`. -/
@[simp]
theorem inv_app {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    (NatIso.mapHomotopyCategory e c).inv.app
        ((HomotopyCategory.quotient C c).obj K) =
      (NatTrans.mapHomotopyCategory e.inv c).app
        ((HomotopyCategory.quotient C c).obj K) := sorry

end mapHomotopyCategory



end CategoryTheory.NatIso
