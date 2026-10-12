/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.RingTheory.Flat.Locus

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The locus where a module is flat over both an intermediate scheme and the base scheme. -/
def flatOverBothLocus {S X Y : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ Y) (g : Y ⟶ S) : Set X :=
  {x : X | flatOverAt ℱ f x ∧ flatOverAt ℱ (f ≫ g) x}

/-- Membership in the simultaneous flatness locus is flatness over both the intermediate
scheme and the base scheme. -/
@[simp]
theorem mem_flatOverBothLocus {S X Y : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    x ∈ flatOverBothLocus ℱ f g ↔
      flatOverAt ℱ f x ∧ flatOverAt ℱ (f ≫ g) x := sorry

/-- The simultaneous flatness locus is the intersection of the two pointwise flatness loci. -/
theorem flatOverBothLocus_eq_inter {S X Y : Scheme.{u}}
    (ℱ : X.Modules) (f : X ⟶ Y) (g : Y ⟶ S) :
    flatOverBothLocus ℱ f g =
      {x : X | flatOverAt ℱ f x} ∩ {x : X | flatOverAt ℱ (f ≫ g) x} := sorry

/-- If `f : X ⟶ S` is locally of finite presentation and `ℱ` is a finitely presented
module on `X`, then the locus where `ℱ` is flat over `S` is open. -/
@[stacks 0399]
theorem isOpen_flatOverAt {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] :
    IsOpen {x : X | flatOverAt ℱ f x} := sorry

end AlgebraicGeometry.Scheme.Modules
