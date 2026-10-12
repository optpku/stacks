/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Comparison
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localization Models for Bounded Derived Single Objects

The canonical single-object functors into bounded derived categories are
defined by lifting the ambient derived single functors.  This module records
the subordinate models obtained by first entering the bounded homotopy
category and then localizing, together with their canonical comparisons.
-/

open CategoryTheory
open scoped CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory

namespace DerivedCategory.singleFunctor

/-- A single object in the homotopy category becomes the corresponding
single object after derived localization. -/
@[stacks 015A]
noncomputable def compQhIso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    HomotopyCategory.singleFunctor C n ⋙ DerivedCategory.Qh ≅
      DerivedCategory.singleFunctor C n :=
  ((SingleFunctors.evaluation C (DerivedCategory C) n).mapIso
    (DerivedCategory.singleFunctorsPostcompQhIso C)).symm

end DerivedCategory.singleFunctor

namespace DerivedCategory.Plus.singleFunctor

/-- The localization model of the degree-`n` single-object functor into
`D⁺(C)`. -/
@[stacks 015A]
noncomputable def fromHomotopy (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    C ⥤ DerivedCategory.Plus C :=
  HomotopyCategory.Plus.singleFunctor C n ⋙ DerivedCategory.Plus.Qh

/-- The bounded-below localization model of a single-object functor is
additive. -/
instance fromHomotopy.additive (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    (fromHomotopy C n).Additive := sorry

namespace fromHomotopy

/-- After bounded-below inclusion, the localization model is the ambient
derived single-object functor. -/
@[stacks 015A]
noncomputable def compInclusionIso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    fromHomotopy C n ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.singleFunctor C n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor C n)
      (DerivedCategory.Plus.QhCompιIsoιCompQh C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomotopyCategory.Plus.singleFunctorCompιIso C n)
        DerivedCategory.Qh ≪≫
      DerivedCategory.singleFunctor.compQhIso C n

/-- The bounded-below localization model is canonically isomorphic to the
canonical bounded-below single-object functor. -/
@[stacks 015A]
noncomputable def iso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    fromHomotopy C n ≅ DerivedCategory.Plus.singleFunctor C n :=
  ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C)).whiskeringRight C).preimageIso
    (compInclusionIso C n ≪≫
      (DerivedCategory.Plus.singleFunctorιIso C n).symm)

end fromHomotopy

end DerivedCategory.Plus.singleFunctor

namespace DerivedCategory.Minus.singleFunctor

/-- The localization model of the degree-`n` single-object functor into
`D⁻(C)`. -/
@[stacks 015A]
noncomputable def fromHomotopy (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    C ⥤ DerivedCategory.Minus C :=
  HomotopyCategory.Minus.singleFunctor C n ⋙ DerivedCategory.Minus.Qh C

/-- The bounded-above localization model of a single-object functor is
additive. -/
instance fromHomotopy.additive (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    (fromHomotopy C n).Additive := sorry

namespace fromHomotopy

/-- After bounded-above inclusion, the localization model is the ambient
derived single-object functor. -/
@[stacks 015A]
noncomputable def compInclusionIso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    fromHomotopy C n ⋙ DerivedCategory.Minus.ι ≅
      DerivedCategory.singleFunctor C n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Minus.singleFunctor C n)
      (DerivedCategory.Minus.Qh.compInclusionIso C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomotopyCategory.Minus.singleFunctorCompιIso C n)
        DerivedCategory.Qh ≪≫
      DerivedCategory.singleFunctor.compQhIso C n

/-- The bounded-above localization model is canonically isomorphic to the
canonical bounded-above single-object functor. -/
@[stacks 015A]
noncomputable def iso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    fromHomotopy C n ≅ DerivedCategory.Minus.singleFunctor C n :=
  ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ DerivedCategory C)).whiskeringRight C).preimageIso
    (compInclusionIso C n ≪≫
      (DerivedCategory.Minus.singleFunctorιIso C n).symm)

end fromHomotopy

end DerivedCategory.Minus.singleFunctor

namespace DerivedCategory.Bounded.singleFunctor

/-- The localization model of the degree-`n` single-object functor into
`Dᵇ(C)`. -/
@[stacks 0FCP]
noncomputable def fromHomotopy (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    C ⥤ DerivedCategory.Bounded C :=
  HomotopyCategory.Bounded.singleFunctor C n ⋙ DerivedCategory.Bounded.Qh C

/-- The bounded localization model of a single-object functor is additive. -/
instance fromHomotopy.additive (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    (fromHomotopy C n).Additive := sorry

namespace fromHomotopy

/-- After bounded inclusion, the localization model is the ambient derived
single-object functor. -/
@[stacks 0FCP]
noncomputable def compInclusionIso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    fromHomotopy C n ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.singleFunctor C n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Bounded.singleFunctor C n)
      (DerivedCategory.Bounded.Qh.compInclusionIso C) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (HomotopyCategory.Bounded.singleFunctorCompιIso C n)
        DerivedCategory.Qh ≪≫
      DerivedCategory.singleFunctor.compQhIso C n

/-- The bounded localization model is canonically isomorphic to the canonical
bounded single-object functor. -/
@[stacks 0FCP]
noncomputable def iso (C : Type u) [Category.{v} C]
    [Abelian C] [HasDerivedCategory.{w} C] (n : ℤ) :
    fromHomotopy C n ≅ DerivedCategory.Bounded.singleFunctor C n :=
  ((Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Bounded.ι : DerivedCategory.Bounded C ⥤ DerivedCategory C)).whiskeringRight C).preimageIso
    (compInclusionIso C n ≪≫
      (DerivedCategory.Bounded.singleFunctorιIso C n).symm)

end fromHomotopy

end DerivedCategory.Bounded.singleFunctor



end CategoryTheory
