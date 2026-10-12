/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Monoidal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleCat

/- Remark 56.3.10: Let A and B be rings, with their module categories equipped with the usual
tensor-product monoidal structures, and let F : ModuleCat Aᵐᵒᵖ ⥤ ModuleCat Bᵐᵒᵖ be a monoidal
functor in the sense of Categories, Definition 4.43.2. Since F(A) is a tensor unit, it is
identified with B, and the action on F(A) gives a multiplicative map φ : A → B. For A = B and
F(M) = M ⊗[A] M, this map is given by φ(a) = a². If F is additive, then φ is a ring map. For
A = B = ℤ and F(M) = M / torsion, one has φ = id_ℤ although F is not the identity functor. If F
is right exact and commutes with direct sums, then F(M) = M ⊗[A, φ] B by Lemma 56.3.1. Thus ring
maps A →+* B are in bijection with isomorphism classes of monoidal functors
ModuleCat Aᵐᵒᵖ ⥤ ModuleCat Bᵐᵒᵖ that commute with all colimits; the reusable classification is
recorded below. -/
@[stacks 0GP2]
#check (ModuleCat.monoidalFunctor_isomorphic_extendScalars :
  ∀ {A B : Type u} [CommRing A] [CommRing B]
    (F : ModuleCat Aᵐᵒᵖ ⥤ ModuleCat Bᵐᵒᵖ) [F.Monoidal],
    rightExactFunctor (ModuleCat Aᵐᵒᵖ) (ModuleCat Bᵐᵒᵖ) F →
      (∀ J : Type u, PreservesColimitsOfShape (Discrete J) F) →
        ∃! φ : A →+* B, ∃ e : F ≅ ModuleCat.extendScalars φ.op,
          CategoryTheory.NatTrans.IsMonoidal e.hom)

section CanonicalChecks

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/- The canonical comparison between the source and target tensor units. -/
#check (Functor.Monoidal.εIso)

/- Extension of scalars along a ring homomorphism. -/
#check (ModuleCat.extendScalars)

/- Extension of scalars is right exact. -/
#check (ModuleCat.extendScalars_rightExact φ)

/- Extension of scalars carries the canonical monoidal structure. -/
#check (inferInstance : (ModuleCat.extendScalars φ).Monoidal)

/- Extension of scalars is a left adjoint. -/
#check (inferInstance : (ModuleCat.extendScalars φ).IsLeftAdjoint)

end CanonicalChecks

end ModuleCat
