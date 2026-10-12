/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Abutment
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.TotalHomologyFunctor

/-!
# Derived homology functor for Cartan--Eilenberg resolutions

This leaf packages the derived abutment as a functor on bundled Cartan--Eilenberg resolutions.
The mapped-total and filtered-total homology functors live in the neutral
`CartanEilenberg.Map.TotalHomologyFunctor` leaf.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution.Bundled

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive]

section Derived

variable [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

/-- Bounded-below total right-derived cohomology, functorial in a bundled
Cartan--Eilenberg resolution through its source complex. -/
@[stacks 015J "derived abutment functor of Cartan-Eilenberg resolutions"]
noncomputable def derivedHomology (n : ℤ) : Bundled A ⥤ B where
  obj X := Functor.RightDerived.Bounded.cohomology F Q X.base n
  map f := Map.derivedHomology F Q f n
  map_id X := Map.derivedHomology_id F Q X.resolution n
  map_comp f g := Map.derivedHomology_comp F Q f g n

/-- Object computation for bounded-below total right-derived cohomology. -/
@[simp, stacks 015J "derived abutment functor of Cartan-Eilenberg resolutions"]
theorem derivedHomology_obj (n : ℤ) (X : Bundled A) :
    (derivedHomology F Q n).obj X =
      Functor.RightDerived.Bounded.cohomology F Q X.base n := sorry

/-- Morphism computation for bounded-below total right-derived cohomology. -/
@[simp, stacks 015J "derived abutment functor of Cartan-Eilenberg resolutions"]
theorem derivedHomology_map (n : ℤ) {X Y : Bundled A} (f : X ⟶ Y) :
    (derivedHomology F Q n).map f = Map.derivedHomology F Q f n := sorry

end Derived

end CochainComplex.CartanEilenbergResolution.Bundled
