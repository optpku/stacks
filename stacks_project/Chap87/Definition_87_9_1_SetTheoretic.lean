module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Set-theoretic size for sheaves on a chosen big fppf site

A sheaf on the fixed site `(Sch/S)_fppf` is a coequalizer of two maps of
representable sheaves when there exist objects `U`, `R` of that same site and
fppf-sheaf surjections `U ⟶ X` and `R ⟶ U ×_X U`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on a chosen big fppf site `(Sch/S)_fppf` is a coequalizer of two maps
between representable sheaves: there exist objects `U`, `R` of the same fixed
site together with fppf-sheaf surjections `U ⟶ X` and `R ⟶ U ×_X U`. -/
class IsCoequalizerOfRepresentables
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop where
  /-- There exist objects `U` and `R` of `(Sch/S)_fppf` and locally surjective
  maps of fppf sheaves from their sheafified representables onto `X` and onto
  `U ×_X U`. -/
  exists_presentation :
    ∃ (U R : 𝒮.bigSite S)
      (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
      (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶ pullback π π),
        Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ

namespace IsCoequalizerOfRepresentables

/-- The sheafified representable of any object of `(Sch/S)_fppf` is a coequalizer
of two maps of representable sheaves, via identity surjections. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S) :
    IsCoequalizerOfRepresentables ((𝒮.bigTopology S).sheafifiedRepresentable U) := sorry

/-- The size condition is equivalent to the existence of objects `U`, `R` of the
fixed site with locally surjective maps `U ⟶ X` and `R ⟶ U ×_X U`. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsCoequalizerOfRepresentables X ↔
      ∃ (U R : 𝒮.bigSite S)
        (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶ pullback π π),
          Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ := sorry

/-- An `IsCoequalizerOfRepresentables` sheaf admits objects `U`, `R` of the fixed
site and locally surjective maps onto `X` and onto `U ×_X U`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    ∃ (U R : 𝒮.bigSite S)
      (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
      (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶ pullback π π),
        Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ := sorry

/-- The size condition is equivalent to `X` being a coequalizer of two maps of
representable sheaves on the same fixed site. -/
theorem iff_isCoequalizer {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsCoequalizerOfRepresentables X ↔
      ∃ (U R : 𝒮.bigSite S)
        (p q : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶
          (𝒮.bigTopology S).sheafifiedRepresentable U)
        (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (hπ : p ≫ π = q ≫ π),
          Nonempty (IsColimit (Cofork.ofπ π hπ)) := sorry

end IsCoequalizerOfRepresentables

end AlgebraicGeometry.ChosenBigFppfSite
