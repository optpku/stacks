/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Separable
public import stacks_project.Chap90.Definition_90_3_2_SmallExtension
public import stacks_project.Chap90.Lemma_90_3_4_Length
public import stacks_project.Chap90.Lemma_90_3_8_Pullback
import StacksCheckRecall

/-!
# Fibre products in the base category

A cospan in `C_Λ` has fibre product in `C_Λ` when a leg is surjective, or when
`k / residueImage Λ k` is separable. Small extensions are stable under the
first projection of such a fibre product.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {A A1 A2 : ArtinianLocalAlgCat Λ k}

/- Lemma 90.3.8 (1): if `f1` or `f2` is surjective, then the algebra fibre product
`AlgHom.pullback f1.hom f2.hom` is an object of `ArtinianLocalAlgCat Λ k`. -/
@[stacks 06GH] #check ArtinianLocalAlgCat.pullback

/-- Lemma 90.3.8 (2): if `f2` is a small extension, then so is the first
projection of the fibre product `A1 ×_A A2 ⟶ A1`. -/
@[stacks 06GH]
instance instIsSmallExtension_pullbackFst (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [IsSmallExtension f2] :
    IsSmallExtension (pullbackFst f1 f2 (Or.inr IsSmallExtension.surjective)) := sorry

/-- If the field extension `k / residueImage Λ k` is separable, then the residue
comparison of `AlgHom.pullback f1.hom f2.hom` is surjective. -/
theorem surjective_pullbackResidueFieldHom_of_separable (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    Function.Surjective (pullbackResidueFieldHom f1 f2) := sorry

/-- Lemma 90.3.8 (3): if the field extension `k / residueImage Λ k` is separable,
then the algebra fibre product `A1 ×_A A2` is an object of `ArtinianLocalAlgCat Λ k`
whose residue identification is the canonical comparison. -/
@[stacks 06GH]
theorem exists_pullback_of_separable (f1 : A1 ⟶ A) (f2 : A2 ⟶ A)
    [Algebra.IsSeparable (Algebra.residueImage Λ k) k] :
    ∃ P : ArtinianLocalAlgCat Λ k,
      P.carrier = AlgHom.pullback f1.hom f2.hom ∧
        HEq P.residueFieldIso.toAlgHom (pullbackResidueFieldHom f1 f2) := sorry

end ArtinianLocalAlgCat
