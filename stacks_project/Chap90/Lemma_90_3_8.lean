module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.CospanPullback
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
@[stacks 06GH] #check (ArtinianLocalAlgCat.pullback :
  (f1 : A1 ⟶ A) → (f2 : A2 ⟶ A) →
    (Function.Surjective f1.hom ∨ Function.Surjective f2.hom) → ArtinianLocalAlgCat Λ k)

/- Lemma 90.3.8 (2): if `f2` is a small extension, then so is the first
projection of the fibre product `A1 ×_A A2 ⟶ A1`. -/
@[stacks 06GH] #check (ArtinianLocalAlgCat.instIsSmallExtension_pullbackFst :
  ∀ (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) [IsSmallExtension f2],
    IsSmallExtension (pullbackFst f1 f2 (Or.inr IsSmallExtension.surjective)))

/- Lemma 90.3.8 (3): if `k / residueImage Λ k` is separable, then the concrete
algebra fibre product is an object with the canonical residue comparison. -/
@[stacks 06GH] #check (ArtinianLocalAlgCat.pullbackOfSeparable_spec :
  ∀ (f1 : A1 ⟶ A) (f2 : A2 ⟶ A) [Algebra.IsSeparable (Algebra.residueImage Λ k) k],
    ((pullbackOfSeparable f1 f2).carrier : Type u) = AlgHom.pullback f1.hom f2.hom ∧
      (pullbackOfSeparable f1 f2).residueFieldIso.toAlgHom = pullbackResidueFieldHom f1 f2)

end ArtinianLocalAlgCat
