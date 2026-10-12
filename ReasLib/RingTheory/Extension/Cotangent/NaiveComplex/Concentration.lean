/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex

/-!
# Concentration of naive cotangent complexes

@stack 07BN
@stack 07BP

The presentation-level naive cotangent complex is two-term.  This leaf exposes its concentration
properties without forcing applications to unfold the chosen chain-complex model.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u v w

namespace Algebra.Extension.NaiveCotangent

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Definition 10.134.1, tag `07BN`: every component of a naive cotangent complex in degree at
least two is a zero object. -/
@[stacks 07BN "higher components are zero"]
theorem componentSuccSuccIsZero (P : Extension.{w} R S) (i : ℕ) :
    IsZero ((complex P).X (i + 2)) := sorry

/-- Definition 10.134.1, tag `07BN`: a component of a naive cotangent complex is a zero object
whenever its degree is neither zero nor one. -/
@[stacks 07BN "two-term concentration"]
theorem componentIsZero (P : Extension.{w} R S) (n : ℕ) (hn_zero : n ≠ 0) (hn_one : n ≠ 1) :
    IsZero ((complex P).X n) := sorry

/-- A subsingleton cotangent space is the zero object in the module category. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
theorem cotangentSpaceIsZero (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace) :
    IsZero (ModuleCat.of.{max v w} S P.CotangentSpace) := sorry

/-- The cotangent-complex map vanishes when the cotangent space is subsingleton. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
theorem cotangentComplex_eq_zero_of_subsingleton
    (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace) :
    P.cotangentComplex = 0 := sorry

/-- The canonical inclusion of first cotangent homology is bijective when the cotangent space is
subsingleton. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
theorem h1Cotangentι_bijective_of_subsingleton
    (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace) :
    Function.Bijective P.h1Cotangentι := sorry

/-- First cotangent homology identifies with the conormal module when the cotangent space is
subsingleton. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
noncomputable def h1CotangentιEquivOfSubsingleton
    (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace) :
    P.H1Cotangent ≃ₗ[S] P.Cotangent :=
  LinearEquiv.ofBijective P.h1Cotangentι (h1Cotangentι_bijective_of_subsingleton P hP)

/-- The degree-zero component of the single complex on the lifted conormal module is zero. -/
@[stacks 07BP "single-complex concentration"]
theorem singleOneComponentZeroIsZero (P : Extension.{w} R S) :
    IsZero
      (((HomologicalComplex.single (ModuleCat.{max v w} S) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of.{max v w} S (Lift P))).X 0) := sorry

/-- Every component in degree at least two of the single complex on the lifted conormal module is
zero. -/
@[stacks 07BP "single-complex concentration"]
theorem singleOneComponentSuccSuccIsZero (P : Extension.{w} R S) (n : ℕ) :
    IsZero
      (((HomologicalComplex.single (ModuleCat.{max v w} S) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of.{max v w} S (Lift P))).X (n + 2)) := sorry

/-- Componentwise comparison from a naive cotangent complex with subsingleton cotangent space to
the single complex on its lifted conormal module. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
noncomputable def componentIsoSingleOne
    (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace) :
    ∀ n : ℕ, (complex P).X n ≅
      ((HomologicalComplex.single (ModuleCat.{max v w} S) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of.{max v w} S (Lift P))).X n
  | 0 =>
      componentZeroIso P ≪≫ (cotangentSpaceIsZero P hP).isoZero ≪≫
        (singleOneComponentZeroIsZero P).isoZero.symm
  | 1 =>
      componentOneIso P ≪≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 1
        (ModuleCat.of.{max v w} S (Lift P))).symm
  | n + 2 =>
      (componentSuccSuccIsZero P n).isoZero ≪≫
        (singleOneComponentSuccSuccIsZero P n).isoZero.symm

/-- The componentwise comparison with the single conormal complex respects differentials. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
theorem componentIsoSingleOne_comm
    (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace)
    (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel i j) :
    (componentIsoSingleOne P hP i).hom ≫
        ((HomologicalComplex.single (ModuleCat.{max v w} S) (ComplexShape.down ℕ) 1).obj
          (ModuleCat.of.{max v w} S (Lift P))).d i j =
      (complex P).d i j ≫ (componentIsoSingleOne P hP j).hom := sorry

/-- A naive cotangent complex with subsingleton cotangent space is homotopy equivalent to the
single complex on its lifted conormal module in degree one. -/
@[stacks 07BP "subsingleton cotangent-space concentration"]
noncomputable def homotopyEquivSingleOneOfSubsingleton
    (P : Extension.{w} R S) (hP : Subsingleton P.CotangentSpace) :
    HomotopyEquiv (complex P)
      ((HomologicalComplex.single (ModuleCat.{max v w} S) (ComplexShape.down ℕ) 1).obj
        (ModuleCat.of.{max v w} S (Lift P))) :=
  HomotopyEquiv.ofIso <|
    HomologicalComplex.Hom.isoOfComponents (componentIsoSingleOne P hP)
      (componentIsoSingleOne_comm P hP)

end Algebra.Extension.NaiveCotangent
