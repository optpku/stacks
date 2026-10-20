module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import ReasLib.CategoryTheory.Limits.Shapes.Pullback.Cube
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits AlgebraicSpace

variable {S : Scheme.{u}} {Y Z Z' X : AlgebraicSpace S}
variable (yZ : Y ⟶ Z) (z'Z : Z' ⟶ Z) (f : X ⟶ Z)

/- 74.11.1.1 (1): the comparison to Y ×_Z X and the projection to Y ×_Z Z'
form the cartesian face over Y. -/
@[stacks 041M] #check
  (CategoryTheory.Limits.pullback.cubeMap_fst_isPullback yZ z'Z f :
    IsPullback (pullback.fst (pullback.snd yZ z'Z) (pullback.snd f z'Z))
      (CategoryTheory.Limits.pullback.cubeMap yZ z'Z f)
      (pullback.fst yZ z'Z) (pullback.fst yZ f))

/- 74.11.1.1 (2): the comparison to Y ×_Z X and the projection to Z' ×_Z X
form the cartesian face over X. -/
@[stacks 041M] #check
  (CategoryTheory.Limits.pullback.cubeMap_snd_isPullback yZ z'Z f :
    IsPullback (CategoryTheory.Limits.pullback.cubeMap yZ z'Z f)
      (pullback.snd (pullback.snd yZ z'Z) (pullback.snd f z'Z))
      (pullback.snd yZ f) (pullback.fst f z'Z))

/- The bottom face of the cube is the cartesian square
Y ×_Z Z' of yZ : Y ⟶ Z and z'Z : Z' ⟶ Z. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback yZ z'Z :
    IsPullback (pullback.fst yZ z'Z) (pullback.snd yZ z'Z) yZ z'Z)

/- The right face is the cartesian square Z' ×_Z X of f : X ⟶ Z
and z'Z : Z' ⟶ Z, with f' the base change pullback.snd f z'Z. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback f z'Z :
    IsPullback (pullback.fst f z'Z) (pullback.snd f z'Z) f z'Z)

/- The front face of the cube is the cartesian square
Y ×_Z X of yZ : Y ⟶ Z and f : X ⟶ Z. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback yZ f :
    IsPullback (pullback.fst yZ f) (pullback.snd yZ f) yZ f)

/- The left face is the cartesian square Y ×_Z Z' ×_Z X of the
base changes pullback.snd yZ z'Z and f' = pullback.snd f z'Z. -/
#check
  (CategoryTheory.IsPullback.of_hasPullback
      (pullback.snd yZ z'Z) (pullback.snd f z'Z) :
    IsPullback (pullback.fst (pullback.snd yZ z'Z) (pullback.snd f z'Z))
      (pullback.snd (pullback.snd yZ z'Z) (pullback.snd f z'Z))
      (pullback.snd yZ z'Z) (pullback.snd f z'Z))
