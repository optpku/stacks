module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import stacks_project.Chap66.Definition_66_18_9_Square
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_26_3_Glueing
public import stacks_project.Chap66.Proposition_66_32_1_Comparison

/-!
# Relative flatness at a point, Comparison-side

A quasi-coherent module on an algebraic space is flat at a point over the target when some
étale scheme presentation reduces the condition to `Scheme.Modules.flatOverAt`. This is the
same étale-chart criterion as `Lemma_67_31_3_FlatOver`, stated using
`Proposition_66_32_1_Comparison` so that it can be imported together with `relativeWeakAss`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A quasi-coherent module `F` on `X` is flat at a point `x` over `Y` if some étale scheme
square over `f` has the restricted module flat at a germ of `U` mapping to `x`. -/
def flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules) (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (sq : EtaleSquare f) (u : sq.left.left.left),
    Points.map sq.left.hom (ofOver.pointsEquiv sq.left.left u) = x ∧
      Scheme.Modules.flatOverAt
        ((restrictFunctor sq.left.hom ⋙
            (schemeEtaleRingedHom sq.left.left).modulePushforward.{u} ⋙
              (smallEtaleToOpensRingedHom sq.left.left.left).modulePushforward.{u} ⋙
                opensToSchemeModules sq.left.left.left).obj F)
        sq.map.left u

/-- Pointwise relative flatness unpacks as the existence of an étale scheme presentation
whose restricted module is relatively flat at a germ mapping to the given point. -/
theorem flatOverAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) (x : Points X) :
    flatOverAt F f x ↔
      ∃ (sq : EtaleSquare f) (u : sq.left.left.left),
        Points.map sq.left.hom (ofOver.pointsEquiv sq.left.left u) = x ∧
          Scheme.Modules.flatOverAt
            ((restrictFunctor sq.left.hom ⋙
                (schemeEtaleRingedHom sq.left.left).modulePushforward.{u} ⋙
                  (smallEtaleToOpensRingedHom sq.left.left.left).modulePushforward.{u} ⋙
                    opensToSchemeModules sq.left.left.left).obj F)
            sq.map.left u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

