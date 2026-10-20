module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Separation

/-! Compatibility checks for separated formal algebraic spaces. -/

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite
open scoped TensorProduct

universe u v

#check (AlgebraicGeometry.sectionTensor :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {U V W : 𝒮.bigAffineSite S} (p : W ⟶ U) (q : W ⟶ V),
    Γ((𝒮.bigAffineToScheme S).obj U, ⊤) ⊗[ℤ]
        Γ((𝒮.bigAffineToScheme S).obj V, ⊤) →+*
      Γ((𝒮.bigAffineToScheme S).obj W, ⊤))

#check (AlgebraicGeometry.sectionTensor_eq :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    {U V W : 𝒮.bigAffineSite S} (p : W ⟶ U) (q : W ⟶ V),
    sectionTensor p q =
      (Algebra.TensorProduct.productMap
          ((𝒮.bigAffineToScheme S).map p).appTop.hom.toIntAlgHom
          ((𝒮.bigAffineToScheme S).map q).appTop.hom.toIntAlgHom).toRingHom)

#check (AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))), Prop)

#check (AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace.instSheafifiedRepresentable :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S),
    IsSeparatedFormalAlgebraicSpace
      ((𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj U)))

#check (AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace.iff :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))),
    IsSeparatedFormalAlgebraicSpace X ↔
      IsFormalAlgebraicSpace X ∧
        ∀ (U V : 𝒮.bigAffineSite S)
          (u : (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
          (v : (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
          ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
            (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
              ((𝒮.bigAffineInclusion S).obj W)),
            e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
                ((𝒮.bigAffineInclusion S).map p) =
              pullback.fst u v ∧
            e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
                ((𝒮.bigAffineInclusion S).map q) =
              pullback.snd u v ∧
            Function.Surjective (sectionTensor p q))

#check (AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace.spec :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsSeparatedFormalAlgebraicSpace X]
    {U V : 𝒮.bigAffineSite S}
    (u : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U) ⟶ X)
    (v : (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj V) ⟶ X),
    ∃ (W : 𝒮.bigAffineSite S) (p : W ⟶ U) (q : W ⟶ V)
      (e : pullback u v ≅ (𝒮.bigTopology S).sheafifiedRepresentable
        ((𝒮.bigAffineInclusion S).obj W)),
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map p) =
        pullback.fst u v ∧
      e.hom ≫ (𝒮.bigTopology S).sheafifiedRepresentableMap
          ((𝒮.bigAffineInclusion S).map q) =
        pullback.snd u v ∧
      Function.Surjective (sectionTensor p q))
