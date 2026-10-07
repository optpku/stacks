module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Data.Countable.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_11_1_Formal
import StacksCheckRecall

/-!
# Remark 87.11.5

The set-theoretic size condition on a sheaf on a fixed big fppf site
`(Sch/S)_fppf` is coequalizer-of-representables. This condition is inherited
by countable directed affine thickening colimits, implies the algebraic space
property for affine-scheme atlases, and follows from a countable étale affine
atlas with quasi-compact diagonal.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

/- Remark 87.11.5 (1): on a fixed big fppf site `(Sch/S)_fppf`, the size
condition used in Definitions 87.9.1 and 87.11.1 is the existence of objects
`U`, `R` of the same site together with fppf-sheaf surjections `U ⟶ X` and
`R ⟶ U ×_X U`, equivalently that `X` is a coequalizer of two maps of
representable sheaves. -/
@[stacks 0AIS] #check IsCoequalizerOfRepresentables

@[stacks 0AIS] #check IsCoequalizerOfRepresentables.iff_isCoequalizer

namespace AlgebraicGeometry.ChosenBigFppfSite
namespace IsCoequalizerOfRepresentables

/-- If a directed affine thickening colimit presentation of `X` has coproduct
of stages represented by an object of `(Sch/S)_fppf`, then `X` satisfies the
coequalizer size condition. -/
theorem of_representableStageCoproduct
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X)
    (hU : ∃ (U : 𝒮.bigSite S)
        (c : Cofan fun i ↦
          (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))
        (hc : IsColimit c),
      Nonempty ((𝒮.bigTopology S).sheafifiedRepresentable U ≅ c.pt)) :
    IsCoequalizerOfRepresentables X := sorry

/-- Remark 87.11.5 (2): if `X` is a directed colimit of affine objects along
thickening transitions as in Definition 87.9.1 (1)(2), the index type `Λ` is
countable, and the coproduct of stages is represented by an object of
`(Sch/S)_fppf`, then the size condition holds. The coproduct map is a
surjection of fppf sheaves, and `U ×_X U` is a closed subscheme of
`U ×_S U` by Lemma 87.9.2; Sets Lemma 3.9.9 supplies such coproducts on
Stacks-style sites. -/
@[stacks 0AIS]
theorem of_countableDirectedColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Countable Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X)
    (hU : ∃ (U : 𝒮.bigSite S)
        (c : Cofan fun i ↦
          (𝒮.bigTopology S).sheafifiedRepresentable
            ((𝒮.bigAffineInclusion S).obj (D.obj i)))
        (hc : IsColimit c),
      Nonempty ((𝒮.bigTopology S).sheafifiedRepresentable U ≅ c.pt)) :
    IsCoequalizerOfRepresentables X := sorry

end IsCoequalizerOfRepresentables

namespace IsAlgebraicSpace

/-- Remark 87.11.5 (3): if `{X_ i ⟶ X}` is an étale jointly surjective atlas
by affine formal algebraic spaces as in Definition 87.11.1, each `X_ i` is
an affine scheme, and `X` satisfies the size condition, then `X` is an
algebraic space on `(Sch/S)_fppf`. The comparison uses a larger site on
which the coproducts of the charts and of the fibre products `X_ i ×_X X_ j`
are representable, then Spaces Lemma 65.15.2. -/
@[stacks 0AIS]
theorem of_affineSchemeAtlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
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
          ((𝒮.bigAffineInclusion S).obj U))) :
    IsAlgebraicSpace X := sorry

end IsAlgebraicSpace

namespace IsCoequalizerOfRepresentables

/-- Remark 87.11.5 (4): if `{X_ i ⟶ X}` satisfies Definition 87.11.1 (1)(2)(3)
with countable index, each chart admits a sheaf-surjective presentation from
an object of `(Sch/S)_fppf` whose coproduct is represented on the same site,
and the diagonal `X ⟶ X ×_S X` is quasi-compact, then `X` satisfies the size
condition. -/
@[stacks 0AIS]
theorem of_countableEtaleAtlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {ι : Type (max u v)} [Countable ι]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c)
    (h_affine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (h_etale : ∀ i, etale (π i))
    (h_surj : Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π))
    (h_diag :
      (MorphismProperty.inverseImage (@QuasiCompact) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X))
    (hU : ∃ (U_ : ι → 𝒮.bigSite S)
        (p : ∀ i, (𝒮.bigTopology S).sheafifiedRepresentable (U_ i) ⟶ X_ i)
        (U : 𝒮.bigSite S)
        (cU : Cofan fun i ↦ (𝒮.bigTopology S).sheafifiedRepresentable (U_ i))
        (hcU : IsColimit cU),
      (∀ i, Sheaf.IsLocallySurjective (p i)) ∧
        Nonempty ((𝒮.bigTopology S).sheafifiedRepresentable U ≅ cU.pt)) :
    IsCoequalizerOfRepresentables X := sorry

end IsCoequalizerOfRepresentables
end AlgebraicGeometry.ChosenBigFppfSite
