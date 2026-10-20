module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.BaseChange

/-!
# Lemma 27.4.1 compatibility entry point

The relative-spectrum base-change construction, natural comparison, and
pointwise computation API are owned by ReasLib.
-/

@[expose] public section

universe u

open CategoryTheory

/- Lemma 27.4.1: base change of the relative spectrum of a quasi-coherent algebra. -/
@[stacks 01LS] #check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A' →
          CategoryTheory.Iso
            (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A')
            (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangePair :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (g : S' ⟶ S) → (A : S.QcAlgebraUnder) →
        (T : AlgebraicGeometry.Scheme.{u}) → Type u)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (g : S' ⟶ S) → (A : S.QcAlgebraUnder) →
        {X Y : AlgebraicGeometry.Scheme.{u}ᵒᵖ} → (a : X ⟶ Y) →
          AlgebraicGeometry.Scheme.relativeSpectrumBaseChangePair g A (Opposite.unop X) →
            AlgebraicGeometry.Scheme.relativeSpectrumBaseChangePair g A (Opposite.unop Y))

#check
  (AlgebraicGeometry.Scheme.RelativeSpectrumPullback :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (g : S' ⟶ S) → (A : S.QcAlgebraUnder) → (A' : S'.QcAlgebraUnder) → Type (u + 1))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap_id :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (g : S' ⟶ S) → (A : S.QcAlgebraUnder) →
        (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ) →
          AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap g A (𝟙 T) = id)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap_comp :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (g : S' ⟶ S) → (A : S.QcAlgebraUnder) →
        {T T' T'' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} →
          (a : T ⟶ T') → (b : T' ⟶ T'') →
            AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap g A (a ≫ b) =
              AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap g A b ∘
                AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap g A a)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (g : S' ⟶ S) → (A : S.QcAlgebraUnder) →
        AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoHomApp :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ) →
            (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A').obj T →
              (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A).obj T)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoInvApp :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ) →
            (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A).obj T →
              (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A').obj T)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso_hom_naturality :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} → (a : T ⟶ T') →
            TypeCat.ofHom
                  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap A' a) ≫
                TypeCat.ofHom
                  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoHomApp
                    A g A' pullbackData T') =
              TypeCat.ofHom
                    (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoHomApp
                      A g A' pullbackData T) ≫
                TypeCat.ofHom
                  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap g A a))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso_inv_naturality :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          {T T' : AlgebraicGeometry.Scheme.{u}ᵒᵖ} → (a : T ⟶ T') →
            TypeCat.ofHom
                  (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctorMap g A a) ≫
                TypeCat.ofHom
                  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoInvApp
                    A g A' pullbackData T') =
              TypeCat.ofHom
                    (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoInvApp
                      A g A' pullbackData T) ≫
                TypeCat.ofHom
                  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorMap A' a))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoHom :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A' →
          (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A' ⟶
            AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoInv :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A' →
          (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A ⟶
            AlgebraicGeometry.Scheme.relativeSpectrumFunctor A'))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso_hom_inv_id :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoHom
                A g A' pullbackData ≫
              AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoInv
                A g A' pullbackData =
            𝟙 (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A'))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso_inv_hom_id :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoInv
                A g A' pullbackData ≫
              AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIsoHom
                A g A' pullbackData =
            𝟙 (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A))

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso_homApp :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ) →
            (x : (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A').obj T) →
              (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso
                    A g A' pullbackData).hom.app T x =
                ⟨x.1, pullbackData.homEquiv x.1 x.2⟩)

#check
  (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso_invApp :
    {S S' : AlgebraicGeometry.Scheme.{u}} →
      (A : S.QcAlgebraUnder) → (g : S' ⟶ S) → (A' : S'.QcAlgebraUnder) →
        (pullbackData : AlgebraicGeometry.Scheme.RelativeSpectrumPullback g A A') →
          (T : AlgebraicGeometry.Scheme.{u}ᵒᵖ) →
            (x : (AlgebraicGeometry.Scheme.relativeSpectrumBaseChangeFunctor g A).obj T) →
              (AlgebraicGeometry.Scheme.relativeSpectrumFunctorBaseChangeIso
                    A g A' pullbackData).inv.app T x =
                ⟨x.1, (pullbackData.homEquiv x.1).symm x.2⟩)
