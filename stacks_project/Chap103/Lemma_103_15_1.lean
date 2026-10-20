/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap103.Lemma_103_15_1_Ringed
public import stacks_project.Chap103.Lemma_103_15_1_Square
import StacksCheckRecall

/-!
A smooth (resp. flat) morphism of algebraic stacks restricts to a continuous
and cocontinuous functor of lisse-étale (resp. flat-fppf) sites, inducing a
morphism of ringed topoi that fills a commutative square with the inclusions
of Lemma 103.14.2 and the associated-étale (resp. inherited-fppf) morphism,
and satisfying the mixed identities `f'_*(g')⁻¹ ≅ g⁻¹ f_*` and
`g'_!(f')⁻¹ ≅ f⁻¹ g_!`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable (f : X ⟶ Y)

section Smooth

variable [Smooth f]

/- Lemma 103.15.1 (1): a smooth morphism of algebraic stacks restricts to a
functor X_lisse,étale ⟶ Y_lisse,étale. -/
@[stacks 07AT]
#check (lisseEtaleMap f)

/- Lemma 103.15.1 (2): the restricted lisse-étale functor is continuous. -/
@[stacks 07AT]
#check (lisseEtaleMap.instIsContinuous f)

/- Lemma 103.15.1 (3): the restricted lisse-étale functor is cocontinuous. -/
@[stacks 07AT]
#check (lisseEtaleMap.instIsCocontinuous f)

/- Lemma 103.15.1 (4): the restricted functor gives a morphism of ringed topoi
f' : Sh(X_lisse,étale) ⟶ Sh(Y_lisse,étale). -/
@[stacks 07AT]
#check (lisseEtaleMap.ringedToposHom f)

/- Lemma 103.15.1 (5): f' fills a commutative square with the lisse-étale
inclusions g', g and the associated-étale morphism f. -/
@[stacks 07AT]
#check (lisseEtaleFunctorialSquare f)

/- Lemma 103.15.1 (6): f'_*(g')⁻¹ ≅ g⁻¹ f_* on sheaves of types. -/
@[stacks 07AT]
#check (lisseEtalePushforwardRestrictionIso f)

/- Lemma 103.15.1 (7): g'_!(f')⁻¹ ≅ f⁻¹ g_! on sheaves of types. -/
@[stacks 07AT]
#check (lisseEtaleLowerShriekInverseImageIso f)

end Smooth

section Flat

variable [Flat f]

/- Lemma 103.15.1 (8): a flat morphism of algebraic stacks restricts to a
functor X_flat,fppf ⟶ Y_flat,fppf. -/
@[stacks 07AT]
#check (flatFppfMap f)

/- Lemma 103.15.1 (9): the restricted flat-fppf functor is continuous. -/
@[stacks 07AT]
#check (flatFppfMap.instIsContinuous f)

/- Lemma 103.15.1 (10): the restricted flat-fppf functor is cocontinuous. -/
@[stacks 07AT]
#check (flatFppfMap.instIsCocontinuous f)

/- Lemma 103.15.1 (11): the restricted functor gives a morphism of ringed topoi
f' : Sh(X_flat,fppf) ⟶ Sh(Y_flat,fppf). -/
@[stacks 07AT]
#check (flatFppfMap.ringedToposHom f)

/- Lemma 103.15.1 (12): f' fills a commutative square with the flat-fppf
inclusions g', g and the inherited-fppf morphism f. -/
@[stacks 07AT]
#check (flatFppfFunctorialSquare f)

/- Lemma 103.15.1 (13): f'_*(g')⁻¹ ≅ g⁻¹ f_* on sheaves of types. -/
@[stacks 07AT]
#check (flatFppfPushforwardRestrictionIso f)

/- Lemma 103.15.1 (14): g'_!(f')⁻¹ ≅ f⁻¹ g_! on sheaves of types. -/
@[stacks 07AT]
#check (flatFppfLowerShriekInverseImageIso f)

end Flat
