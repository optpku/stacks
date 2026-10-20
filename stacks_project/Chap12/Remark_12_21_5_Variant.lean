module

public import ReasLib.CategoryTheory.Homology.ExactCouple.Shifted.PageFiltration
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory
namespace ShiftedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S T : C ≌ C}
variable (K : Derived.Construction T) (X : ShiftedExactCouple S T)

/- Remark 12.21.5 (Variant) (1) (tag `0AMJ`): a shifted exact couple packages the exact complex
`T E ⟶ T A ⟶ A ⟶ S E ⟶ S A`; its page-one differential is `E ⟶ S E`. -/
@[stacks 0AMJ "(1)"]
#check (ShiftedExactCouple S T)

#check (X.Tf_comp_tAlpha : T.functor.map X.f ≫ X.tAlpha = 0)
#check (X.tAlpha_comp_g : X.tAlpha ≫ X.g = 0)
#check (X.g_comp_Sf : X.g ≫ S.functor.map X.f = 0)
#check (X.exact_Tf_tAlpha :
  (ShortComplex.mk (T.functor.map X.f) X.tAlpha X.Tf_comp_tAlpha).Exact)
#check (X.exact_tAlpha_g :
  (ShortComplex.mk X.tAlpha X.g X.tAlpha_comp_g).Exact)
#check (X.exact_g_Sf :
  (ShortComplex.mk X.g (S.functor.map X.f) X.g_comp_Sf).Exact)
#check (X.d : X.E ⟶ S.functor.obj X.E)
#check (X.α : X.A ⟶ T.inverse.obj X.A)
#check (X.page : ShiftedDifferentialObject S.functor)
#check @Hom.pageMap
#check (pageFunctor S T :
  ShiftedExactCouple S T ⥤ ShiftedDifferentialObject S.functor)

/- Remark 12.21.5 (Variant) (2): deriving changes the page shift from `S` to `T ∘ S`, replaces
`A` by `image (Tα)`, and replaces `E` by page-one homology. -/
@[stacks 0AMJ "(2)"]
#check (K.derived X : ShiftedExactCouple (S.trans T) T)

#check ((K.derived X).A : C)
#check ((K.derived X).E : C)
#check ((K.derived X).tAlpha : T.functor.obj (K.derived X).A ⟶ (K.derived X).A)
#check ((K.derived X).f : (K.derived X).E ⟶ (K.derived X).A)
#check ((K.derived X).g : (K.derived X).A ⟶ (S.trans T).functor.obj (K.derived X).E)

/- Remark 12.21.5 (Variant) (3): iteration gives a shifted spectral sequence whose page-`r`
shift is `T^(r - 1) ∘ S`. -/
@[stacks 0AMJ "(3)"]
#check (K.associatedSpectralSequence X : ShiftedSpectralSequence (ShiftedSpectralSequence.pageShift S T))
#check (ShiftedSpectralSequence.PageShift.eq_trans_pow S T :
  ∀ q : ℕ+, ShiftedSpectralSequence.pageShift S T q = S.trans (T ^ (q.natPred : ℤ)))

#check (Derived.Page.complex K X :
  ∀ r : ℕ,
    (K.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩ =
      (K.data (K.iterate X r)).page)
#check (Derived.Page.obj K X :
  ∀ r : ℕ,
    ((K.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩).obj =
      (K.iterate X r).E)
#check (Derived.Page.differential K X :
  ∀ r : ℕ,
    ((K.associatedSpectralSequence X).page ⟨r + 1, Nat.succ_pos _⟩).d =
      (K.iterate X r).d)

variable (r : ℕ)

#check (TAlphaSource.zero X : X.tAlphaSource 0 = X.A)
#check (TAlphaSource.succ X r :
  X.tAlphaSource (r + 1) = T.functor.obj (X.tAlphaSource r))
#check (TAlphaSource.eq_pow X r :
  X.tAlphaSource r = (T ^ (r : ℤ)).functor.obj X.A)
#check (X.tAlphaIterate r : X.tAlphaSource r ⟶ X.A)
#check (TAlphaIterate.zero X : X.tAlphaIterate 0 = 𝟙 X.A)
#check (TAlphaIterate.succ X r :
  X.tAlphaIterate (r + 1) = T.functor.map (X.tAlphaIterate r) ≫ X.tAlpha)
#check (AlphaTarget.zero X : X.alphaTarget 0 = X.A)
#check (AlphaTarget.succ X r :
  X.alphaTarget (r + 1) = T.inverse.obj (X.alphaTarget r))
#check (AlphaTarget.eq_pow X r :
  X.alphaTarget r = (T ^ (-(r : ℤ))).functor.obj X.A)
#check (X.alphaIterate r : X.A ⟶ X.alphaTarget r)
#check (AlphaIterate.zero X : X.alphaIterate 0 = 𝟙 X.A)
#check (AlphaIterate.succ X r :
  X.alphaIterate (r + 1) = X.α ≫ T.inverse.map (X.alphaIterate r))

/- Remark 12.21.5 (Variant) (4): `Z_{r+1}` is the inverse image under `f` of the image of the
forward translated composite `Tα ≫ ... ≫ Tʳα`. -/
@[stacks 0AMJ "(4)"]
#check (Associated.cycle_eq K X r :
  (K.associatedSpectralSequence X).cycle (Nat.succPNat r) = X.cyclesSubobject r)

/- Remark 12.21.5 (Variant) (5): `S B_{r+1}` is the image under `g` of the kernel of the backward
translated composite `α ≫ ... ≫ T⁻ʳ⁺¹α`. -/
@[stacks 0AMJ "(5)"]
#check (Associated.boundary_map_eq K X r :
  Limits.imageSubobject
      (S.functor.map ((K.associatedSpectralSequence X).boundary (Nat.succPNat r)).arrow) =
    X.shiftedBoundariesSubobject r)

end ShiftedExactCouple
end CategoryTheory
