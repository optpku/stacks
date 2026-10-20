module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.KanExtension.Comparison
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Hom
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
import Mathlib.CategoryTheory.Abelian.Basic
import StacksCheckRecall

@[expose] public section

/-!
@stack 0190

# Source-facing facade for Lemma 14.22.2

The reusable Hom descriptions, degreewise Kan-extension decompositions, structure maps, and
comparison coefficients are owned by
`ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.KanExtension`.
-/

open CategoryTheory CategoryTheory.Limits Opposite SimplexCategory Simplicial
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory

/- The ambient comparison is owned independently of the concentrated-object computation. -/
#check SimplicialObject.Truncated.adjointTriple
#check SimplicialObject.Truncated.skToCosk.eq_leftToRight

namespace SimplicialObject.Truncated.concentrated

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (B : A) (k n : ℕ) (V : SimplicialObject.Truncated A k)

/- Lemma 14.22.2 (1): maps from the concentrated object are top-degree maps satisfying
the face-vanishing condition. -/
@[stacks 0190 "Lemma 14.22.2 (1): maps from the concentrated object"]
#check (homFromEquiv B V : (concentrated B k ⟶ V) ≃ FaceMap B V)

/- Lemma 14.22.2 (1): maps to the concentrated object are top-degree maps satisfying
the degeneracy-vanishing condition. -/
@[stacks 0190 "Lemma 14.22.2 (1): maps to the concentrated object"]
#check (homToEquiv B V : (V ⟶ concentrated B k) ≃ DegeneracyMap V B)

/- Lemma 14.22.2 (2): the degree-`n` skeleton is the biproduct indexed by epimorphisms
`[n] ⟶ [k]`. -/
@[stacks 0190 "Lemma 14.22.2 (2): degreewise skeleton biproduct"]
#check (skeleton.biproduct.iso B k n :
  ((SimplicialObject.Truncated.sk k).obj (concentrated B k)).obj (op ⦋n⦌) ≅
    ⨁ fun _ : EpiHom ⦋n⦌ ⦋k⦌ ↦ B)

/- The reusable decomposition is natural in the coefficient object. -/
@[stacks 0190 "Lemma 14.22.2 (2): natural skeleton biproduct decomposition"]
#check (skeleton.biproduct.natIso (A := A) k n :
  skeleton.degree.functor (A := A) k n ≅
    Limits.biproduct.diagonal (C := A) (EpiHom ⦋n⦌ ⦋k⦌))
#check (skeleton.biproduct.natIso.app (A := A) k n B)

variable {n' : ℕ} (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)

/- The reusable structure-map formula treats the epic and nonepic cases uniformly through
partial precomposition of the summand index. -/
@[stacks 0190 "Lemma 14.22.2 (3): unified skeleton structure map"]
#check (skeleton.map_ι B f a :
  skeleton.ι B a ≫ ((SimplicialObject.Truncated.sk k).obj (concentrated B k)).map f.op =
    (a.precomp f).elim 0 (fun c ↦ skeleton.ι B c))

variable (h_epi : Epi (f ≫ a.hom)) (h_not_epi : ¬ Epi (f ≫ a.hom))

/- Lemma 14.22.2 (3): a skeleton structure map carries an epic summand to the summand
indexed by the composite. -/
@[stacks 0190 "Lemma 14.22.2 (3): skeleton map on an epic composite"]
#check (skeleton.map_ι_of_epi.explicit B f a h_epi :
  skeleton.ι B a ≫ ((SimplicialObject.Truncated.sk k).obj (concentrated B k)).map f.op =
    skeleton.ι B ⟨f ≫ a.hom, h_epi⟩)

/- Lemma 14.22.2 (3): a skeleton structure map is zero on a summand whose composite is
not epic. -/
@[stacks 0190 "Lemma 14.22.2 (3): skeleton map on a non-epic composite"]
#check (skeleton.map_ι_of_not_epi B f a h_not_epi :
  skeleton.ι B a ≫ ((SimplicialObject.Truncated.sk k).obj (concentrated B k)).map f.op = 0)

/- Lemma 14.22.2 (4): the degree-`n` coskeleton is the biproduct indexed by
monomorphisms `[k] ⟶ [n]`. -/
@[stacks 0190 "Lemma 14.22.2 (4): degreewise coskeleton biproduct"]
#check (coskeleton.biproduct.iso B k n :
  ((SimplicialObject.Truncated.cosk k).obj (concentrated B k)).obj (op ⦋n⦌) ≅
    ⨁ fun _ : MonoHom ⦋k⦌ ⦋n⦌ ↦ B)

/- The reusable decomposition is natural in the coefficient object. -/
@[stacks 0190 "Lemma 14.22.2 (4): natural coskeleton biproduct decomposition"]
#check (coskeleton.biproduct.natIso (A := A) k n :
  coskeleton.degree.functor (A := A) k n ≅
    Limits.biproduct.diagonal (C := A) (MonoHom ⦋k⦌ ⦋n⦌))
#check (coskeleton.biproduct.natIso.app (A := A) k n B)

variable (b : MonoHom ⦋k⦌ ⦋n⦌)

/- The reusable dual formula treats the monic and nonmonic cases uniformly through partial
postcomposition of the factor index. -/
@[stacks 0190 "Lemma 14.22.2 (5): unified coskeleton structure map"]
#check (coskeleton.map_π B f b :
  ((SimplicialObject.Truncated.cosk k).obj (concentrated B k)).map f.op ≫
      coskeleton.π B b =
    (b.postcomp f).elim 0 (fun c ↦ coskeleton.π B c))

variable (h_mono : Mono (b.hom ≫ f)) (h_not_mono : ¬ Mono (b.hom ≫ f))

/- Lemma 14.22.2 (5): a coskeleton structure map carries a monic projection to the
projection indexed by the composite. -/
@[stacks 0190 "Lemma 14.22.2 (5): coskeleton map on a monic composite"]
#check (coskeleton.map_π_of_mono.explicit B f b h_mono :
  ((SimplicialObject.Truncated.cosk k).obj (concentrated B k)).map f.op ≫
      coskeleton.π B b =
    coskeleton.π B ⟨b.hom ≫ f, h_mono⟩)

/- Lemma 14.22.2 (5): a coskeleton structure map followed by a projection is zero when
the composite is not monic. -/
@[stacks 0190 "Lemma 14.22.2 (5): coskeleton map on a non-monic composite"]
#check (coskeleton.map_π_of_not_mono B f b h_not_mono :
  ((SimplicialObject.Truncated.cosk k).obj (concentrated B k)).map f.op ≫
      coskeleton.π B b = 0)

variable (a' : EpiHom ⦋n⦌ ⦋k⦌) (b' : MonoHom ⦋k⦌ ⦋n⦌)

/- Lemma 14.22.2 (6): a comparison coefficient is the identity exactly when the
monomorphism is a section of the epimorphism, and is zero otherwise. -/
@[stacks 0190 "Lemma 14.22.2 (6): comparison matrix coefficient"]
#check (comparison.coeff B a' b' :
  skeleton.ι B a' ≫ ((skToCosk (A := A) k).app (concentrated B k)).app (op ⦋n⦌) ≫
      coskeleton.π B b' =
    if b'.hom ≫ a'.hom = 𝟙 ⦋k⦌ then 𝟙 B else 0)

/- The reusable comparison matrix and its coefficient formula are natural in `B`. -/
@[stacks 0190 "Lemma 14.22.2 (6): natural comparison matrix"]
#check (comparison.matrix.hom (A := A) k n :
  Limits.biproduct.diagonal (C := A) (EpiHom ⦋n⦌ ⦋k⦌) ⟶
    Limits.biproduct.diagonal (C := A) (MonoHom ⦋k⦌ ⦋n⦌))

/- Each matrix entry is already an equality of natural transformations. -/
@[stacks 0190 "Lemma 14.22.2 (6): natural comparison matrix coefficient"]
#check (comparison.matrix.coeff (A := A) a' b' :
  Limits.biproduct.diagonal.ι (C := A) a' ≫
      comparison.matrix.hom (A := A) k n ≫
      Limits.biproduct.diagonal.π (C := A) b' =
    if b'.hom ≫ a'.hom = 𝟙 ⦋k⦌ then 𝟙 (𝟭 A) else 0)

/- The reusable comparison API also exposes monicity one simplicial degree at a time. -/
#check (comparison.degree.mono B k n :
  Mono (((skToCosk (A := A) k).app (concentrated B k)).app (op ⦋n⦌)))

/- Lemma 14.22.2 (7): the canonical comparison from the skeleton to the coskeleton of
the concentrated truncated object is a monomorphism. -/
@[stacks 0190 "Lemma 14.22.2 (7): comparison monomorphism"]
#check (comparison.mono B k : Mono ((skToCosk (A := A) k).app (concentrated B k)))

end SimplicialObject.Truncated.concentrated

end CategoryTheory
