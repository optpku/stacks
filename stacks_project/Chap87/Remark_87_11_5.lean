module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Presentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Size
import StacksCheckRecall

/-!
# Remark 87.11.5

On a fixed size-closed big fppf site, the presentation condition is equivalent
to being a coequalizer of representables. Directed affine thickening colimits
with represented stage coproducts satisfy it, in particular countable systems.
An affine-scheme étale atlas gives an algebraic space, and a countable étale
atlas by affine formal algebraic spaces with quasi-compact diagonal gives the
presentation condition.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/- Remark 87.11.5: the fixed-site size condition is a locally surjective
representable presentation of a sheaf and its covering kernel pair,
equivalently a coequalizer of two maps between representable sheaves. -/
@[stacks 0AIS] #check (AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables.iff_isCoequalizer :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))),
    IsCoequalizerOfRepresentables X ↔
      ∃ (U R : 𝒮.bigSite S)
        (p q : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶
          (𝒮.bigTopology S).sheafifiedRepresentable U)
        (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (hπ : p ≫ π = q ≫ π),
          Nonempty (IsColimit (Cofork.ofπ π hπ)))

#check (AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables :
    Sheaf (𝒮.bigTopology S) (Type (max u v)) → Prop)

#check (AlgebraicGeometry.ChosenBigFppfSite.exists_representable_countableCoproduct :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {ι : Type (max u v)} [Countable ι] (A : ι → 𝒮.bigSite S),
    ∃ (U : 𝒮.bigSite S)
      (c : Cofan fun i ↦ (𝒮.bigTopology S).sheafifiedRepresentable (A i))
      (_ : IsColimit c),
      Nonempty ((𝒮.bigTopology S).sheafifiedRepresentable U ≅ c.pt))

#check (AlgebraicGeometry.IsDirectedAffineThickeningColimit.isLocallySurjective_stageCoproduct :
    ∀ {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (c : Cocone (D ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (h : IsDirectedAffineThickeningColimit D c.pt)
    (cU : Cofan fun i ↦ (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj (D.obj i)))
    (hcU : IsColimit cU),
    Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hcU fun i ↦ c.ι.app i))

#check (AlgebraicGeometry.IsDirectedAffineThickeningColimit.isClosedImmersion_diag :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X),
    (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X))

#check (AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables.of_representableStageCoproduct :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X)
    (hU : ∃ (U : 𝒮.bigSite S)
        (c : Cofan fun i ↦
          (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))
        (hc : IsColimit c),
      Nonempty ((𝒮.bigTopology S).sheafifiedRepresentable U ≅ c.pt)),
    IsCoequalizerOfRepresentables X)

#check (AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables.of_countableDirectedColimit :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Countable Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X),
    IsCoequalizerOfRepresentables X)

#check (AlgebraicGeometry.ChosenBigFppfSite.IsAlgebraicSpace.of_affineSchemeAtlas :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {ι : Type (max u v)}
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCoequalizerOfRepresentables X]
    (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c)
    (h_affine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (h_etale : ∀ i, etale (π i))
    (h_surj : Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π))
    (h_scheme : ∀ i, ∃ U : 𝒮.bigAffineSite S,
      Nonempty (X_ i ≅
        (𝒮.bigTopology S).sheafifiedRepresentable
          ((𝒮.bigAffineInclusion S).obj U))),
    IsAlgebraicSpace X)

#check (AlgebraicGeometry.ChosenBigFppfSite.IsCoequalizerOfRepresentables.of_countableEtaleAtlas :
    ∀ (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {ι : Type (max u v)} [Countable ι]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c)
    (h_affine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (h_etale : ∀ i, etale (π i))
    (h_surj : Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π))
    (h_diag :
      (MorphismProperty.inverseImage (@QuasiCompact) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X)),
    IsCoequalizerOfRepresentables X)
