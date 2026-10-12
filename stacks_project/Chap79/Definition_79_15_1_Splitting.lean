/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap78.Lemma_78_16_1_Stabilizer
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Splitting

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

noncomputable section

universe u

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.openOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left), Over B)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.openInclusion :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left), G.openOver P ⟶ G.R)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictSource :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left), G.openOver P ⟶ G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictTarget :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (P : OpenSubspace G.R.left), G.openOver P ⟶ G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceTargetFiber :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (u : Points G.U.left), Set (Points G.R.left))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerFiberPoints :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (u : Points G.U.left), Set (Points G.R.left))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.FiniteOpenSubgroupoid :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S},
    GroupoidAlgebraicSpace B → Type (u + 1))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.StrongSplitting :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Type (u + 1))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Splitting :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Type (u + 1))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.QuasiSplitting :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Type (u + 1))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.IsStronglySplitOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Prop)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.IsSplitOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Prop)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.IsQuasiSplitOver :
  ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (u : Points G.U.left), Prop)

end
