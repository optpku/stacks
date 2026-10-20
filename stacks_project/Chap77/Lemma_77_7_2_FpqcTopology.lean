module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sites.Fpqc
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Fpqc site of schemes over an algebraic space

The fpqc covering families of schemes over an algebraic space `B` are the
families whose images under the forgetful functor to schemes over `S` cover
for `Scheme.fpqcTopology.over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

open AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (B : AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.fpqcPrecoverage B :
  Precoverage (SchemeOver B))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.fpqcTopology B :
  GrothendieckTopology (SchemeOver B))

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.fpqcTopology_def B :
  SchemeOver.fpqcTopology B = (SchemeOver.fpqcPrecoverage B).toGrothendieck)

variable {ι : Type u} {U : SchemeOver B} {V : ι → SchemeOver B}
variable {f : ∀ i, V i ⟶ U}

#check (AlgebraicGeometry.AlgebraicSpace.SchemeOver.ofArrows_mem_fpqcPrecoverage_iff
    (B := B) (V := V) (f := f) :
  Presieve.ofArrows V f ∈ SchemeOver.fpqcPrecoverage B U ↔
    Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
      (Scheme.fpqcTopology.over S).toPrecoverage U.left)
