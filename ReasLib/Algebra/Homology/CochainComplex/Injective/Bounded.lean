module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.Fixed
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded complexes of injective objects

@stack 0A5S

This file packages a cochain complex supported in a fixed interval and injective in every degree.
The bundled owner makes its bounds and injectivity available to instance search, so derived-category
consumers do not have to reconstruct these canonical facts with local instances.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CochainComplex

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C]

/-- Complexes supported in `[a, b]` whose terms are injective objects. -/
@[stacks 0A5S "bounded injective representative"]
def injectiveIn (a b : ℤ) : ObjectProperty (CochainComplex C ℤ) :=
  (strictlyGE C a ⊓ strictlyLE C b) ⊓ termsIn (isInjective C)

/-- Membership in `injectiveIn C a b` is the conjunction of the two support bounds and
termwise injectivity. -/
theorem mem_injectiveIn_iff (I : CochainComplex C ℤ) (a b : ℤ) :
    injectiveIn C a b I ↔
      I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧ ∀ i : ℤ, Injective (I.X i) := sorry

/-- The full subcategory of cochain complexes of injectives supported in `[a, b]`. -/
@[stacks 0A5S "bounded injective representatives"]
abbrev InjectiveIn (a b : ℤ) :=
  (injectiveIn C a b).FullSubcategory

namespace InjectiveIn

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The canonical inclusion of fixed-amplitude injective complexes. -/
abbrev ι (a b : ℤ) : InjectiveIn C a b ⥤ CochainComplex C ℤ :=
  ObjectProperty.ι _

/-- A bundled fixed-amplitude injective complex carries its lower support bound. -/
instance isStrictlyGE (a b : ℤ) (I : InjectiveIn C a b) :
    I.obj.IsStrictlyGE a := sorry

/-- A bundled fixed-amplitude injective complex carries its upper support bound. -/
instance isStrictlyLE (a b : ℤ) (I : InjectiveIn C a b) :
    I.obj.IsStrictlyLE b := sorry

/-- Every term of a bundled fixed-amplitude injective complex is injective. -/
instance injective (a b : ℤ) (I : InjectiveIn C a b) (i : ℤ) :
    Injective (I.obj.X i) := sorry

/-- A bounded-below complex of injectives is canonically K-injective. -/
instance isKInjective {A : Type u} [Category.{v} A] [Abelian A]
    (a b : ℤ) (I : InjectiveIn A a b) :
    I.obj.IsKInjective := sorry

end InjectiveIn

end CochainComplex
