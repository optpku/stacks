module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Size
public import ReasLib.CategoryTheory.Sites.SheafifiedRepresentable

/-!
# Fixed-site presentation conditions

The fixed-site presentation condition for sheaves on a chosen big fppf site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on a chosen big fppf site `(Sch/S)_fppf` is a coequalizer of two maps
between representable sheaves from the same fixed site. -/
class IsCoequalizerOfRepresentables
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop where
  /-- There are locally surjective maps from representable sheaves of objects
  `U` and `R` onto `X` and `U ×_X U`, respectively. -/
  exists_presentation :
    ∃ (U R : 𝒮.bigSite S)
      (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
      (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶ pullback π π),
        Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ

namespace IsCoequalizerOfRepresentables

/-- Every sheafified representable of the fixed site satisfies the presentation
condition. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigSite S) :
    IsCoequalizerOfRepresentables ((𝒮.bigTopology S).sheafifiedRepresentable U) := sorry

/-- The fixed-site presentation condition is equivalent to its explicit
existence specification. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsCoequalizerOfRepresentables X ↔
      ∃ (U R : 𝒮.bigSite S)
        (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
        (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶ pullback π π),
          Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ := sorry

/-- An explicitly presented sheaf has locally surjective maps from two objects
of the fixed site onto it and its self-pullback. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsCoequalizerOfRepresentables X] :
    ∃ (U R : 𝒮.bigSite S)
      (π : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X)
      (σ : (𝒮.bigTopology S).sheafifiedRepresentable R ⟶ pullback π π),
        Sheaf.IsLocallySurjective π ∧ Sheaf.IsLocallySurjective σ := sorry

/-- The fixed-site presentation condition is equivalent to a coequalizer of two
maps between sheafified representables on a size-closed chosen big site. -/
theorem iff_isCoequalizer {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (h𝒮 : ChosenBigSite.IsSizeClosed 𝒮)
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
