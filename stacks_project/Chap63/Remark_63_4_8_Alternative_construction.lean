/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Open
public import stacks_project.Chap63.Remark_63_4_8_Alternative_construction_Cech
public import stacks_project.Chap63.Remark_63_4_8_Alternative_construction_Cokernel
import StacksCheckRecall

/-!
# Alternative construction of locally quasi-finite lower shriek

Remark 63.4.8: for a locally quasi-finite morphism, `f_!` may be recovered as
the cokernel of the penultimate Čech map of separated restrictions, for example
along an affine open covering of the source.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open TopologicalSpace

universe u

/- Remark 63.4.8 (Alternative construction) (1): Let `f : X ⟶ Y` be a locally
quasi-finite morphism of schemes. Given an open covering `𝒰` of `X` such that
each restriction `(𝒰 i).ι ≫ f` is separated, the functor `f_!` is the cokernel
of the penultimate map
`⊕_{i0,i1} f_{i0 i1,!}(F|_{X_{i0 i1}}) ⟶ ⊕_{i0} f_{i0,!}(F|_{X_{i0}})`,
where the summands are formed with the separated construction
`etaleLowerShriek` of Section 63.3. -/
@[stacks 0F5I]
#check lowerShriekCechCokernelFunctor

/- Remark 63.4.8 (Alternative construction) (2): Computing stalks of this
cokernel by the separated formula `etaleLowerShriekStalkIso` of Lemma 63.3.17
recovers the coproduct formula `(f_! F)_ȳ ≅ ⊕_{f(x̄)=ȳ} F_x̄` of
Lemma 63.4.5. -/
@[stacks 0F5I]
#check lowerShriekCechCokernelStalkIso

namespace AlgebraicGeometry.Scheme.Etale

/-- The affine open covering of a scheme, as an indexed family of affine
opens. -/
noncomputable def affineOpensCover (X : Scheme.{u}) : X.affineCover.I₀ → X.Opens :=
  fun i ↦ (X.affineCover.f i).opensRange

/-- The affine open covering is an open covering of `X`. -/
theorem isOpenCover_affineOpensCover (X : Scheme.{u}) :
    IsOpenCover (affineOpensCover X) :=
  sorry

/-- Each member of the affine open covering is an affine open. -/
instance isAffine_affineOpensCover (X : Scheme.{u}) (i : X.affineCover.I₀) :
    IsAffine (affineOpensCover X i) :=
  sorry

/-- Affine members of `affineOpensCover` are affine opens. -/
theorem isAffineOpen_affineOpensCover (X : Scheme.{u})
    (i : X.affineCover.I₀) :
    IsAffineOpen (affineOpensCover X i) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
