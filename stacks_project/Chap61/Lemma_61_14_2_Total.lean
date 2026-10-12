/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.Hypercovering.Cech.Cohomology
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Total hypercovering Čech complexes

This leaf assembles the integer-indexed row, double complex, and total complex of a
fixed-target hypercovering Čech construction, together with the singleton weakly
contractible hypothesis used to identify `RΓ(U, E)` with `Tot(s(ℰ(K)))`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape HomologicalComplex HomologicalComplex₂
open DerivedCategory.Plus (Q)
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C} {U : C}

/-- A hypercovering of `U` is degreewise a singleton family of weakly contractible objects
when each `K.family n` is indexed by a singleton and the unique source object is weakly
contractible. -/
structure IsWeaklyContractibleSingleton (K : Hypercovering.{w} J U) : Prop where
  /-- Each degree of `K` has at least one index. -/
  nonempty_index : ∀ n : ℕ, Nonempty (K.family n).index
  /-- Each degree of `K` has at most one index. -/
  subsingleton_index : ∀ n : ℕ, Subsingleton (K.family n).index
  /-- Every member of each degree of `K` is weakly contractible. -/
  isWeaklyContractible :
    ∀ n : ℕ, ∀ i : (K.family n).index,
      J.IsWeaklyContractible ((K.family n).obj i).left

namespace IsWeaklyContractibleSingleton

/-- Package a degreewise unique weakly contractible hypercovering as
`IsWeaklyContractibleSingleton`. -/
def ofUnique (K : Hypercovering.{w} J U) [∀ n : ℕ, Unique (K.family n).index]
    (hW : ∀ n : ℕ, ∀ i : (K.family n).index,
      J.IsWeaklyContractible ((K.family n).obj i).left) :
    IsWeaklyContractibleSingleton K where
  nonempty_index _ := inferInstance
  subsingleton_index _ := inferInstance
  isWeaklyContractible := hW

/-- The singleton weakly contractible condition is the conjunction of its three defining
clauses. -/
theorem iff (K : Hypercovering.{w} J U) :
    IsWeaklyContractibleSingleton K ↔
      (∀ n : ℕ, Nonempty (K.family n).index) ∧
        (∀ n : ℕ, Subsingleton (K.family n).index) ∧
          (∀ n : ℕ, ∀ i : (K.family n).index,
            J.IsWeaklyContractible ((K.family n).obj i).left) := sorry

/-- The unique source object `U_n` in degree `n` of a degreewise singleton hypercovering. -/
def obj (K : Hypercovering.{w} J U) [∀ n : ℕ, Unique (K.family n).index] (n : ℕ) : C :=
  ((K.family n).obj default).left

/-- Every member of the degree-`n` family is the unique source object `obj K n`. -/
theorem obj_spec (K : Hypercovering.{w} J U) [∀ n : ℕ, Unique (K.family n).index]
    (n : ℕ) (i : (K.family n).index) :
    ((K.family n).obj i).left = obj K n := sorry

/-- The unique source object in each degree of a singleton weakly contractible hypercovering is
weakly contractible. -/
theorem isWeaklyContractible_obj (K : Hypercovering.{w} J U)
    [∀ n : ℕ, Unique (K.family n).index] (hK : IsWeaklyContractibleSingleton K) (n : ℕ) :
    J.IsWeaklyContractible (obj K n) := sorry

end IsWeaklyContractibleSingleton

end CategoryTheory.Hypercovering

namespace CategoryTheory.Hypercovering.Cech

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{max w v}]
variable {U : C}

/-- Under a degreewise unique index, degree `n` of the hypercovering Čech complex is the
universe-lifted section group over the unique source object. -/
theorem complex_obj_iso_sections (K : Hypercovering.{w} J U)
    [∀ n : ℕ, Unique (K.family n).index]
    (I : Sheaf J AddCommGrpCat.{max w v}) (n : ℕ) :
    IsIsomorphic ((complex K I).X n)
      ((AddCommGrpCat.uliftFunctor.{u, max w v}).obj
        (I.obj.obj (op (IsWeaklyContractibleSingleton.obj K n)))) := sorry

/-- The integer-indexed hypercovering Čech row, obtained by extending the nonnegative Čech
complex by zero. -/
abbrev rowFunctor (K : Hypercovering.{w} J U) :
    Sheaf J AddCommGrpCat.{max w v} ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  complexInCoefficients K ⋙ embeddingUpNat.extendFunctor AddCommGrpCat.{max u v w}

/-- Evaluating the hypercovering Čech row recovers extension by zero of the nonnegative Čech
complex. -/
theorem rowFunctor_obj (K : Hypercovering.{w} J U)
    (F : Sheaf J AddCommGrpCat.{max w v}) :
    (rowFunctor K).obj F = ((complexInCoefficients K).obj F).extend embeddingUpNat := sorry

/-- The hypercovering Čech row preserves zero morphisms. -/
instance rowFunctor_preservesZeroMorphisms (K : Hypercovering.{w} J U) :
    (rowFunctor K).PreservesZeroMorphisms := sorry

/-- The hypercovering Čech bicomplex functor on integer-indexed complexes of abelian sheaves. -/
abbrev doubleFunctor (K : Hypercovering.{w} J U) :
    CochainComplex (Sheaf J AddCommGrpCat.{max w v}) ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{max u v w} (up ℤ) (up ℤ) :=
  (rowFunctor K).mapHomologicalComplex (up ℤ)

/-- Evaluating the hypercovering Čech bicomplex applies the Čech row degreewise. -/
theorem doubleFunctor_obj (K : Hypercovering.{w} J U)
    (ℰ : CochainComplex (Sheaf J AddCommGrpCat.{max w v}) ℤ) :
    (doubleFunctor K).obj ℰ = ((rowFunctor K).mapHomologicalComplex (up ℤ)).obj ℰ := sorry

/-- Sheaves of abelian groups valued in the hypercovering coefficient universe form an abelian
category. -/
instance sheafAddCommGrp_abelian :
    Abelian (Sheaf J AddCommGrpCat.{max w v}) :=
  sheafIsAbelian

/-- Bounded-below derived sections `RΓ(U, -)`, viewed in `D(Ab)` at the sheaf coefficient
universe. -/
noncomputable abbrev derivedSections (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))] :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v}) ⥤
      DerivedCategory AddCommGrpCat.{max w v} :=
  Functor.totalRightDerived
    ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
    DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v})) ⋙
  DerivedCategory.Plus.ι

/-- `derivedSections` is bounded-below `RΓ` followed by `Plus.ι`. -/
theorem derivedSections_comp (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))] :
    derivedSections J U =
      Functor.totalRightDerived
        ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
        DerivedCategory.Plus.Qh
        (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v})) ⋙
      DerivedCategory.Plus.ι := sorry

/-- Bounded-below derived sections after the coefficient universe lift used by
`complexInCoefficients`. -/
noncomputable abbrev derivedSectionsUlift (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))] :
    DerivedCategory.Plus (Sheaf J AddCommGrpCat.{max w v}) ⥤
      DerivedCategory AddCommGrpCat.{max u v w} :=
  derivedSections J U ⋙ (AddCommGrpCat.uliftFunctor.{u, max w v}).mapDerivedCategory

/-- `derivedSectionsUlift` is `derivedSections` followed by `uliftFunctor.mapDerivedCategory`. -/
theorem derivedSectionsUlift_comp (J : GrothendieckTopology C) (U : C)
    [HasSheafify J AddCommGrpCat.{max w v}]
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))] :
    derivedSectionsUlift J U =
      derivedSections J U ⋙
        (AddCommGrpCat.uliftFunctor.{u, max w v}).mapDerivedCategory := sorry

variable [DecidableEq ℤ]
variable [∀ (L : HomologicalComplex₂ AddCommGrpCat.{max u v w} (up ℤ) (up ℤ)),
  L.HasTotal (up ℤ)]

/-- The total complex `Tot(s(ℰ(K)))` of the hypercovering Čech bicomplex. -/
abbrev totalFunctor (K : Hypercovering.{w} J U) :
    CochainComplex (Sheaf J AddCommGrpCat.{max w v}) ℤ ⥤
      CochainComplex AddCommGrpCat.{max u v w} ℤ :=
  doubleFunctor K ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{max u v w} (up ℤ) (up ℤ) (up ℤ)

/-- Evaluating the hypercovering total Čech functor recovers the total complex of the Čech
bicomplex. -/
theorem totalFunctor_obj (K : Hypercovering.{w} J U)
    (ℰ : CochainComplex (Sheaf J AddCommGrpCat.{max w v}) ℤ) :
    (totalFunctor K).obj ℰ =
      HomologicalComplex₂.total ((doubleFunctor K).obj ℰ) (up ℤ) := sorry

/-- The total complex of the hypercovering Čech bicomplex of a bounded-below complex of abelian
sheaves remains bounded below. -/
theorem totalPlus_obj_mem (K : Hypercovering.{w} J U)
    (ℰ : CochainComplex.Plus (Sheaf J AddCommGrpCat.{max w v})) :
    CochainComplex.plus AddCommGrpCat.{max u v w}
      ((CochainComplex.Plus.ι (Sheaf J AddCommGrpCat.{max w v}) ⋙ totalFunctor K).obj ℰ) :=
  sorry

/-- The bounded-below total hypercovering Čech functor. -/
def totalPlus (K : Hypercovering.{w} J U) :
    CochainComplex.Plus (Sheaf J AddCommGrpCat.{max w v}) ⥤
      CochainComplex.Plus AddCommGrpCat.{max u v w} :=
  (CochainComplex.plus AddCommGrpCat.{max u v w}).lift
    (CochainComplex.Plus.ι (Sheaf J AddCommGrpCat.{max w v}) ⋙ totalFunctor K)
    (totalPlus_obj_mem K)

/-- Forgetting the bounded-below structure after `totalPlus` recovers `totalFunctor`. -/
theorem totalPlus_comp_ι (K : Hypercovering.{w} J U) :
    totalPlus K ⋙ CochainComplex.Plus.ι AddCommGrpCat.{max u v w} =
      CochainComplex.Plus.ι (Sheaf J AddCommGrpCat.{max w v}) ⋙ totalFunctor K := sorry

/-- If `K` is a degreewise singleton weakly contractible hypercovering of `U` and `ℰ` is a
bounded-below complex of abelian sheaves, then `RΓ(U, ℰ)` is isomorphic in `D(Ab)` to
`Tot(s(ℰ(K)))` after lifting sections to the Čech coefficient universe. -/
theorem isIsomorphic_rGamma_total (K : Hypercovering.{w} J U)
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor J U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf J AddCommGrpCat.{max w v}))]
    [IsGrothendieckAbelian (Sheaf J AddCommGrpCat.{max w v})]
    (hK : IsWeaklyContractibleSingleton K)
    (ℰ : CochainComplex.Plus (Sheaf J AddCommGrpCat.{max w v})) :
    IsIsomorphic
      ((derivedSectionsUlift J U).obj (Q.obj ℰ))
      (DerivedCategory.Q.obj ((totalFunctor K).obj ℰ.obj)) := sorry

end CategoryTheory.Hypercovering.Cech

end
