/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer

/-!
# The stabilizer action on groupoid arrows

The stabilizer of a groupoid in algebraic spaces acts on its arrow space over the
target by groupoid composition.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- The arrow space of `G`, regarded as an object over `G.U` through the target map. -/
def arrowsOverTarget : Over G.U :=
  Over.mk G.t

/-- The structure map of `arrowsOverTarget G` is the target map of `G`. -/
theorem arrowsOverTarget_hom :
    (arrowsOverTarget G).hom = G.t := sorry

/-- The stabilizer component of a pair in
`G.stabilizer.X ⊗ arrowsOverTarget G`, included in the arrow space. -/
def actionFirst :
    (G.stabilizer.X ⊗ arrowsOverTarget G).left ⟶ G.R :=
  (fst G.stabilizer.X (arrowsOverTarget G)).left ≫
    G.toPreRelation.stabilizerToArrows

/-- The arrow component of a pair in `G.stabilizer.X ⊗ arrowsOverTarget G`. -/
def actionSecond :
    (G.stabilizer.X ⊗ arrowsOverTarget G).left ⟶ G.R :=
  (snd G.stabilizer.X (arrowsOverTarget G)).left

/-- A stabilizer arrow and an arrow over the same target form a composable pair. -/
theorem actionPair_condition :
    actionFirst G ≫ G.s = actionSecond G ≫ G.t := sorry

/-- The canonical map from the action product to the space of composable arrows. -/
def actionPair :
    (G.stabilizer.X ⊗ arrowsOverTarget G).left ⟶ pullback G.s G.t :=
  pullback.lift (actionFirst G) (actionSecond G) (actionPair_condition G)

/-- The first projection of `actionPair G` is the included stabilizer arrow. -/
theorem actionPair_fst :
    actionPair G ≫ pullback.fst G.s G.t = actionFirst G := sorry

/-- The second projection of `actionPair G` is the arrow being acted upon. -/
theorem actionPair_snd :
    actionPair G ≫ pullback.snd G.s G.t = actionSecond G := sorry

/-- Composition with a stabilizer arrow preserves the target of the acted-on arrow. -/
theorem actionHom_condition :
    (actionPair G ≫ G.c) ≫ G.t =
      (G.stabilizer.X ⊗ arrowsOverTarget G).hom := sorry

/-- The canonical action morphism induced by the groupoid composition `G.c`. -/
def actionHom :
    G.stabilizer.X ⊗ arrowsOverTarget G ⟶ arrowsOverTarget G :=
  Over.homMk (actionPair G ≫ G.c) (actionHom_condition G)

/-- The underlying algebraic-space map of `actionHom G` is the composite induced by `G.c`. -/
theorem actionHom_left :
    (actionHom G).left = actionPair G ≫ G.c := sorry

/-- The action morphism satisfies the identity-action law. -/
theorem actionHom_one_smul :
    η[G.stabilizer.X] ⊵ₗ arrowsOverTarget G ≫ actionHom G =
      (λₗ (arrowsOverTarget G)).hom := sorry

/-- The action morphism is compatible with stabilizer multiplication. -/
theorem actionHom_mul_smul :
    μ[G.stabilizer.X] ⊵ₗ arrowsOverTarget G ≫ actionHom G =
      (αₗ G.stabilizer.X G.stabilizer.X (arrowsOverTarget G)).hom ≫
        G.stabilizer.X ⊴ₗ actionHom G ≫ actionHom G := sorry

/-- The module-object structure on arrows over the target induced by `actionHom G`. -/
@[reducible]
def actionModObj : ModObj G.stabilizer.X (arrowsOverTarget G) where
  smul := actionHom G
  one_smul := actionHom_one_smul G
  mul_smul := actionHom_mul_smul G

/-- The canonical action of the stabilizer on arrows over the target. -/
def stabilizerAction : Mod (Over G.U) G.stabilizer.X where
  X := arrowsOverTarget G
  mod := actionModObj G

/-- The object underlying `stabilizerAction G` is the arrow space over the target. -/
theorem stabilizerAction_X :
    (stabilizerAction G).X = arrowsOverTarget G := sorry

/-- The stored action morphism of `stabilizerAction G` is `actionHom G`. -/
theorem stabilizerAction_smul :
    (stabilizerAction G).mod.smul = actionHom G := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
