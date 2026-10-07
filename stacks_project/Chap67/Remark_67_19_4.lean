module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversallyInjective.Separated
public import stacks_project.Chap67.Remark_67_19_4_Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
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
@[stacks 05VS] #check toAffineLine

/- Remark 67.19.4 (3): `toAffineLine` is an isomorphism away from `0`. -/
@[stacks 05VS] #check isIso_over_punctured

/- Remark 67.19.4 (4): there is a unique point of `X` lying above `0`. -/
@[stacks 05VS] #check unique_point_over_origin

/- Remark 67.19.4 (5): `toAffineLine` is a universally injective morphism of
algebraic spaces. -/
@[stacks 05VS] #check universallyInjective_toAffineLine

/- Remark 67.19.4 (6): `toAffineLine` is not separated, since `X` is not
separated. -/
@[stacks 05VS] #check not_separated_toAffineLine
