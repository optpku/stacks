/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Lemma_60_7_4_Category
public import Mathlib.AlgebraicGeometry.Pullbacks

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

@[expose] public section

universe u

namespace DividedPowerScheme.Pullback

/-- The underlying scheme map from a divided-power pullback square to the
ordinary scheme pullback. -/
noncomputable def baseComparison
    {S T T' T'' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S)
    (g : DividedPowerScheme.Hom T'' T) (g' : DividedPowerScheme.Hom T'' T')
    (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f') :
    T''.scheme ⟶ pullback f.base f'.base :=
  pullback.lift g.base g'.base
    ((DividedPowerScheme.Hom.comp_base g f).symm.trans
      ((congrArg DividedPowerScheme.Hom.base h.w).trans
        (DividedPowerScheme.Hom.comp_base g' f')))

/-- The first pullback projection of `baseComparison`. -/
lemma baseComparison_fst
    {S T T' T'' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S)
    (g : DividedPowerScheme.Hom T'' T) (g' : DividedPowerScheme.Hom T'' T')
    (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f') :
    baseComparison f f' g g' h ≫ pullback.fst f.base f'.base = g.base := sorry

/-- The second pullback projection of `baseComparison`. -/
lemma baseComparison_snd
    {S T T' T'' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S)
    (g : DividedPowerScheme.Hom T'' T) (g' : DividedPowerScheme.Hom T'' T')
    (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f') :
    baseComparison f f' g g' h ≫ pullback.snd f.base f'.base = g'.base := sorry

/-- The canonical map from the zero fibre of a divided-power pullback square
to the ordinary pullback of the two zero fibres. -/
noncomputable def zeroFiberComparison
    {S T T' T'' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S)
    (g : DividedPowerScheme.Hom T'' T) (g' : DividedPowerScheme.Hom T'' T')
    (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f') :
    T''.ideal.subscheme ⟶ pullback f.zeroFiberMap f'.zeroFiberMap :=
  pullback.lift g.zeroFiberMap g'.zeroFiberMap
    ((DividedPowerScheme.Hom.zeroFiberMap_comp g f).symm.trans
      ((congrArg DividedPowerScheme.Hom.zeroFiberMap h.w).trans
        (DividedPowerScheme.Hom.zeroFiberMap_comp g' f')))

/-- The first projection of `zeroFiberComparison`. -/
lemma zeroFiberComparison_fst
    {S T T' T'' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S)
    (g : DividedPowerScheme.Hom T'' T) (g' : DividedPowerScheme.Hom T'' T')
    (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f') :
    zeroFiberComparison f f' g g' h ≫
        pullback.fst f.zeroFiberMap f'.zeroFiberMap = g.zeroFiberMap := sorry

/-- The second projection of `zeroFiberComparison`. -/
lemma zeroFiberComparison_snd
    {S T T' T'' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S) (f' : DividedPowerScheme.Hom T' S)
    (g : DividedPowerScheme.Hom T'' T) (g' : DividedPowerScheme.Hom T'' T')
    (h : @CategoryTheory.IsPullback DividedPowerScheme _ T'' T T' S g g' f f') :
    zeroFiberComparison f f' g g' h ≫
        pullback.snd f.zeroFiberMap f'.zeroFiberMap = g'.zeroFiberMap := sorry

end DividedPowerScheme.Pullback
