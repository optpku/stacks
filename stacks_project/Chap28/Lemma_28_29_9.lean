module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.BasicOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

#check
  (@AlgebraicGeometry.IsOpenImmersion.exists_affineOpen_mappingTo_basicOpen :
    ∀ {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U) [IsOpenImmersion i] (w : W),
      ∃ Wi : W.affineOpens, w ∈ (Wi : W.Opens) ∧ ∃ f : Γ(U, ⊤),
        Scheme.Hom.opensRange ((Wi : W.Opens).ι ≫ i) = U.basicOpen f)

#check
  (@AlgebraicGeometry.IsOpenImmersion.exists_basicOpen_mappingTo_basicOpen :
    ∀ {U W : Scheme.{u}} [IsAffine U] (i : W ⟶ U) [IsOpenImmersion i]
      (Wi : W.affineOpens) (f : Γ(U, ⊤))
      (hWi : Scheme.Hom.opensRange ((Wi : W.Opens).ι ≫ i) = U.basicOpen f)
      (a : Γ(W, (Wi : W.Opens))),
      ∃ f' : Γ(U, ⊤),
        Scheme.Hom.opensRange ((W.basicOpen a).ι ≫ i) = U.basicOpen f')

/- Lemma 28.29.9: Let `U` and `V` be affine schemes and let `W ⟶ U` and `W ⟶ V` be open
immersions. Every `w : W` has an affine open neighborhood that maps to a basic open of both
`U` and `V`. -/
@[stacks 0H9B] #check
  (@AlgebraicGeometry.IsOpenImmersion.exists_affineOpen_mappingTo_basicOpens :
    ∀ {U V W : Scheme.{u}} [IsAffine U] [IsAffine V]
      (i : W ⟶ U) (j : W ⟶ V) [IsOpenImmersion i] [IsOpenImmersion j] (w : W),
      ∃ W' : W.affineOpens, w ∈ (W' : W.Opens) ∧
        ∃ f : Γ(U, ⊤), ∃ g : Γ(V, ⊤),
          Scheme.Hom.opensRange ((W' : W.Opens).ι ≫ i) = U.basicOpen f ∧
            Scheme.Hom.opensRange ((W' : W.Opens).ι ≫ j) = V.basicOpen g)
