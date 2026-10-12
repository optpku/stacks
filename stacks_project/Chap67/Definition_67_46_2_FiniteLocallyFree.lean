/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_29_1_RingedSite
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine

/-!
# Finite locally free morphisms of algebraic spaces

A morphism of algebraic spaces is finite locally free when it is affine and the
direct image of its structure sheaf is a finite locally free module on the
target. Rank (also called degree) is the constant-rank refinement of that
module condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The direct image of the structure sheaf, viewed as a module on the target
algebraic space. -/
noncomputable def pushforwardStructureModule {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Y.Modules :=
  (Modules.pushforward f).obj (SheafOfModules.unit (structureSheaf X) : X.Modules)

/-- The pushforward of the structure sheaf is the image of `𝒪_X` under module
pushforward. -/
theorem pushforwardStructureModule_obj {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    pushforwardStructureModule f =
      (Modules.pushforward f).obj (SheafOfModules.unit (structureSheaf X)) :=
  sorry

end Hom

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is finite locally free
if it is affine and `f_* 𝒪_X` is a finite locally free `𝒪_Y`-module. -/
class FiniteLocallyFree {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop extends Affine f where
  /-- The pushforward structure sheaf is finite locally free. -/
  pushforward_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f)

/-- A morphism of algebraic spaces is finite locally free if and only if it is
affine and its pushforward structure sheaf is finite locally free. -/
theorem finiteLocallyFree_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FiniteLocallyFree f ↔
      Affine f ∧ SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f) :=
  sorry

namespace FiniteLocallyFree

/-- The identity morphism of an algebraic space is finite locally free. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : FiniteLocallyFree (𝟙 X) :=
  sorry

/-- An isomorphism of algebraic spaces is finite locally free. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : FiniteLocallyFree f :=
  sorry

/-- A finite locally free morphism supplies finite local freeness of its
pushforward structure sheaf to typeclass search. -/
instance pushforwardStructureModule {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [h : FiniteLocallyFree f] :
    SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f) :=
  h.pushforward_isFiniteLocallyFree

/-- A finite locally free morphism is affine and has finite locally free
pushforward structure sheaf. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteLocallyFree f] :
    Affine f ∧ SheafOfModules.IsFiniteLocallyFree (Hom.pushforwardStructureModule f) :=
  sorry

end FiniteLocallyFree

/-- A finite locally free morphism `f : X ⟶ Y` of algebraic spaces over `S` has
rank or degree `d` if `f_* 𝒪_X` is finite locally free of rank `d`. -/
class FiniteLocallyFreeOfRank {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) : Prop extends FiniteLocallyFree f where
  /-- The pushforward structure sheaf has rank `d`. -/
  pushforward_isFiniteLocallyFreeOfRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank d (Hom.pushforwardStructureModule f)

/-- A morphism of algebraic spaces is finite locally free of rank `d` if and
only if it is finite locally free and its pushforward structure sheaf has rank
`d`. -/
theorem finiteLocallyFreeOfRank_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) :
    FiniteLocallyFreeOfRank f d ↔
      FiniteLocallyFree f ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank d (Hom.pushforwardStructureModule f) :=
  sorry

namespace FiniteLocallyFreeOfRank

/-- The identity morphism of an algebraic space is finite locally free of rank
`1`. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FiniteLocallyFreeOfRank (𝟙 X) 1 :=
  sorry

/-- A finite locally free morphism of rank `d` supplies fixed finite local rank
of its pushforward structure sheaf to typeclass search. -/
instance pushforwardStructureModule {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) [h : FiniteLocallyFreeOfRank f d] :
    SheafOfModules.IsFiniteLocallyFreeOfRank d (Hom.pushforwardStructureModule f) :=
  h.pushforward_isFiniteLocallyFreeOfRank

/-- A finite locally free morphism of rank `d` is finite locally free and has
pushforward structure sheaf of rank `d`. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [FiniteLocallyFreeOfRank f d] :
    FiniteLocallyFree f ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank d (Hom.pushforwardStructureModule f) :=
  sorry

end FiniteLocallyFreeOfRank

end AlgebraicGeometry.AlgebraicSpace
