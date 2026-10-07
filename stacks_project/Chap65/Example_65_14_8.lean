module

public import stacks_project.Chap65.Example_65_14_8_Action
public import stacks_project.Chap65.Example_65_14_8_Space
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace.AffineLineTranslation

universe u

/- Example 65.14.8 (1): for a characteristic-zero field `k`, `ℤ` acts on `U = 𝔸¹_k` by
translation `n(x) = x + n`. -/
@[stacks 02Z7]
#check action

/- Example 65.14.8 (2): the only fixed point of a nontrivial translation is the generic
point of the affine line. -/
@[stacks 02Z7]
#check
  (fixed_iff_genericPoint :
    ∀ (k : Type u) [Field k] [CharZero k] {n : group},
      n ≠ 1 → ∀ u : (cover k).left,
        (action k n).hom.left u = u ↔ u = genericPoint (cover k).left)

/- Example 65.14.8 (3): characteristic zero makes `ℤ` inject into the automorphism group
of the field `k(x)`. -/
@[stacks 02Z7]
#check
  (injective_genericResidueAut :
    ∀ (k : Type u) [Field k] [CharZero k], Function.Injective (genericResidueAut k))

/- Example 65.14.8 (4): the quotient `X = 𝔸¹_k / ℤ` is the fppf sheaf of the translation
action. -/
@[stacks 02Z7]
#check sheafOfPoints

/- Example 65.14.8 (5): the morphism `γ : Spec(k(x)) ⟶ X` of the generic point of the
affine line into the quotient. -/
@[stacks 02Z7]
#check genericHom

/- Example 65.14.8 (6): `γ` does not factor through any monomorphism `Spec(L) ⟶ X` of the
spectrum of a field to `X`. -/
@[stacks 02Z7]
#check not_exists_mono_factor

/- Example 65.14.8 (7): since `ℤ` has no nontrivial finite subgroups, Lemma 65.14.6 implies
that any such factorization has `k(x) = L`. -/
@[stacks 02Z7]
#check isIso_of_mono_factor

/- Example 65.14.8 (8): `γ` is not a monomorphism. -/
@[stacks 02Z7]
#check not_mono_genericHom

/- Example 65.14.8 (9): `Spec(k(x)) ×_X Spec(k(x)) ≅ Spec(k(x)) × ℤ`. -/
@[stacks 02Z7]
#check
  (instIsIso_genericPullbackIso_inv :
    ∀ (k : Type u) [Field k] [CharZero k], IsIso (genericPullbackIso_inv k))
