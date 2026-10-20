module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Size

/-!
# Representable presentations on size-closed big fppf sites

Directed affine thickening colimits and countable étale atlases give
representable presentations of sheaves on a fixed size-closed big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- The sheaf coproduct of a countable family of representables is represented
by an object of the same size-closed big fppf site. -/
theorem ChosenBigFppfSite.exists_representable_countableCoproduct
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {ι : Type (max u v)} [Countable ι] (A : ι → 𝒮.bigSite S) :
    ∃ (U : 𝒮.bigSite S)
      (c : Cofan fun i ↦ (𝒮.bigTopology S).sheafifiedRepresentable (A i))
      (_ : IsColimit c),
      Nonempty ((𝒮.bigTopology S).sheafifiedRepresentable U ≅ c.pt) := sorry

namespace IsDirectedAffineThickeningColimit

/-- For a directed affine thickening diagram, the canonical morphism from the
coproduct of its stages to its sheaf colimit is locally surjective. -/
theorem isLocallySurjective_stageCoproduct
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    (c : Cocone (D ⋙ 𝒮.bigAffineInclusion S ⋙
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor))
    (hc : IsColimit c) (h : IsDirectedAffineThickeningColimit D c.pt)
    (cU : Cofan fun i ↦ (𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj (D.obj i)))
    (hcU : IsColimit cU) :
    Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hcU fun i ↦ c.ι.app i) := sorry

/-- The diagonal of a directed affine thickening colimit is relatively
representable by closed immersions on a size-closed big fppf site; its base
change along a represented covering product is the closed covering kernel pair. -/
theorem isClosedImmersion_diag
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X) :
    (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) := sorry

end IsDirectedAffineThickeningColimit

namespace ChosenBigFppfSite
namespace IsCoequalizerOfRepresentables

/-- A directed affine thickening colimit satisfies the fixed-site presentation
condition if the coproduct of its stages is represented on the size-closed site. -/
theorem of_representableStageCoproduct
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
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

/-- A countable directed colimit of affine objects along thickenings satisfies
the fixed-site presentation condition on a size-closed big fppf site. -/
theorem of_countableDirectedColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)] [Countable Λ]
    (D : Λ ⥤ 𝒮.bigAffineSite S)
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (h : IsDirectedAffineThickeningColimit D X) :
    IsCoequalizerOfRepresentables X := sorry

end IsCoequalizerOfRepresentables

namespace IsAlgebraicSpace

/-- A sheaf satisfying the fixed-site presentation condition and admitting a
jointly locally surjective étale atlas by affine schemes is an algebraic space. -/
theorem of_affineSchemeAtlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
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

/-- A countable jointly locally surjective étale atlas by affine formal
algebraic spaces and a quasi-compact diagonal give the fixed-site presentation
condition on a size-closed big fppf site. -/
theorem of_countableEtaleAtlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
    {ι : Type (max u v)} [Countable ι]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c)
    (h_affine : ∀ i, IsAffineFormalAlgebraicSpace (X_ i))
    (h_etale : ∀ i, etale (π i))
    (h_surj : Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π))
    (h_diag :
      (MorphismProperty.inverseImage (@QuasiCompact) (𝒮.bigToScheme S)).relative
        (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X)) :
    IsCoequalizerOfRepresentables X := sorry

end IsCoequalizerOfRepresentables
end ChosenBigFppfSite

end AlgebraicGeometry
