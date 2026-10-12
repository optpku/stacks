/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.StructureSheaf
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap75.Remark_75_6_3
public import stacks_project.Chap86.«86_3_2_1_Trace»

/-!
# Uncoherated sheafy trace on the affine line

The sheafy-trace morphism of 86.3.2.1 need not be an isomorphism in `D(𝒪_Y)`
before applying the coherator `DQ_Y`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.MonoidalClosed
open CategoryTheory.Functor.LaxMonoidal

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Example 86.3.4: the statement of Lemma 86.3.3 is not true without applying the
coherator `DQ_Y`. On the affine line over `Spec ℤ`, with `L` and `K` the transported
structure sheaves, the uncoherated sheafy-trace map is not an isomorphism. See Duality
for Schemes, Example 48.3.7. -/
@[stacks 0GG3]
theorem affineLineSheafyTrace_not_iso :
    let YSch := Spec (CommRingCat.of ℤ)
    let XSch := Spec (CommRingCat.of (Polynomial ℤ))
    let fSch := Spec.map (CommRingCat.ofHom Polynomial.C)
    let Y := ofOver (Over.mk (𝟙 YSch))
    let X := ofOver (Over.mk fSch)
    let f := ofOverHomMk fSch (Category.comp_id fSch)
    let L := (ofOverEpsilonStar (Over.mk fSch)).obj
      (Scheme.DerivedQCoh.structureSheaf XSch)
    let K := (ofOverEpsilonStar (Over.mk (𝟙 YSch))).obj
      (Scheme.DerivedQCoh.structureSheaf YSch)
    ∀ [QuasiCompact f] [QuasiSeparated f]
      [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]
      [MonoidalClosed (ModuleDerived X)] [MonoidalClosed (ModuleDerived Y)]
      [Functor.LaxMonoidal (moduleDerivedPushforward f)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X) (adj : pushforwardCohomologyIn f ⊣ a),
      ¬ IsIso (sheafyTrace f a adj L K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
