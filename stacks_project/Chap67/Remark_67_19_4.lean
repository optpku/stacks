module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyInjective.Separated
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.SquareMorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

universe u

/- Remark 67.19.4 (1): a universally injective morphism of schemes is separated,
see Morphisms, Lemma 29.10.3. -/
@[stacks 05VS] #check
  (@AlgebraicGeometry.universallyInjective_isSeparated :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S}
      [AlgebraicGeometry.UniversallyInjective f], AlgebraicGeometry.IsSeparated f)

/- Remark 67.19.4 (2): the algebraic space `X = 𝔸¹_k / {x ∼ -x | x ≠ 0}` of
Spaces, Example 65.14.1 comes equipped with a morphism `toAffineLine : X ⟶ 𝔸¹_k`
which maps the point with coordinate `x` to the point with coordinate `x²`. -/
@[stacks 05VS] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.toAffineLine :
    ∀ (k : Type u) [Field k], sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k))

/- Remark 67.19.4 (3): `toAffineLine` is an isomorphism away from `0`. -/
@[stacks 05VS] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.isIso_over_punctured :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      IsIso
        (pullback.snd (toAffineLine k)
          ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (puncturedι k))))

/- Remark 67.19.4 (4): there is a unique point of `X` lying above `0`. -/
@[stacks 05VS] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.unique_point_over_origin :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)]
      (K : Type u) [Field K] (σ : Spec (CommRingCat.of K) ⟶ base k),
      Nonempty
          ((pullback (toAffineLine k)
              ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
                (originToCover k))).obj.obj
            (op (Over.mk σ))) ∧
        Subsingleton
          ((pullback (toAffineLine k)
              ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
                (originToCover k))).obj.obj
            (op (Over.mk σ))))

/- Remark 67.19.4 (5): `toAffineLine` is a universally injective morphism of
algebraic spaces. -/
@[stacks 05VS] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.universallyInjective_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      (MorphismProperty.over (@Surjective)).relative uliftYoneda.{u + 1}
        (pullback.diagonal (toAffineLine k)).hom)

/- Remark 67.19.4 (6): `toAffineLine` is not separated, since `X` is not
separated. -/
@[stacks 05VS] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.not_separated_toAffineLine :
    ∀ (k : Type u) [Field k] [NeZero (2 : k)],
      ¬ (MorphismProperty.over (@IsClosedImmersion)).relative uliftYoneda.{u + 1}
          (pullback.diagonal (toAffineLine k)).hom)
