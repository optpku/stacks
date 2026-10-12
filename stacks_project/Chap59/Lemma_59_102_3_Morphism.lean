/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Comparison

/-!
# Big ph to small étale comparison morphisms

The bundled morphism of topoi `a_S = π_S ∘ ε_S` from the big ph topos of `S` to
the small étale topos, together with its inverse-image identification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale.SmallToBig
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

/-- The identity on `Over S` is continuous from the big étale topology to the
big fppf topology. -/
instance identity_etale_isContinuous_fppf (S : Scheme.{u}) :
    Functor.IsContinuous (𝟭 (Over S))
      (S.overGrothendieckTopology @Etale) (Scheme.fppfTopology.over S) :=
  (StandardTopology.toFppf_isMorphismOfSites .etale S).toIsContinuous

/-- The identity on `Over S` is continuous from the big étale topology to the
big ph topology. -/
instance identity_etale_isContinuous_ph (S : Scheme.{u}) :
    Functor.IsContinuous (𝟭 (Over S))
      (S.overGrothendieckTopology @Etale) (Scheme.bigPhSite S) :=
  Functor.isContinuous_comp' (Functor.rightUnitor (𝟭 (Over S)))
    (S.overGrothendieckTopology @Etale)
    (Scheme.fppfTopology.over S)
    (Scheme.bigPhSite S)

/-- Relocalization from the small étale site of `S` is continuous for the big
ph topology, as the composite of étale relocalization with the identity site
functor to ph. -/
instance relocalizationFunctor_isContinuous_ph (S : Scheme.{u}) :
    Functor.IsContinuous (relocalizationFunctor (𝟙 S))
      S.smallEtaleTopology (Scheme.bigPhSite S) :=
  Functor.isContinuous_comp' (Functor.rightUnitor (relocalizationFunctor (𝟙 S)))
    S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
    (Scheme.bigPhSite S)

/-- The morphism of topoi `a_S : Sh((Sch/S)_ph) ⟶ Sh(S_étale)` obtained by composing
the small-to-big étale morphism `π_S = siteMorphismOfTopoi S` with the ph-to-étale
comparison `ε_S = standardComparison .etale S`. -/
noncomputable abbrev toSmallEtale (X : Scheme.{u}) :
    MorphismOfTopoiIn X.smallEtaleTopology (Scheme.bigPhSite X) :=
  MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (standardComparison .etale X)

/-- `toSmallEtale X` is the composite `π_X ∘ ε_X`. -/
theorem toSmallEtale_eq_comp (X : Scheme.{u}) :
    toSmallEtale X =
      MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (standardComparison .etale X) :=
  sorry

/-- Inverse image along `toSmallEtale X` is the composite `π_X⁻¹ ⋙ ε_X⁻¹`. -/
@[simp]
theorem toSmallEtale_inverseImage (X : Scheme.{u}) :
    (toSmallEtale X)⁻¹ =
      (siteMorphismOfTopoi X)⁻¹ ⋙ (standardComparison .etale X)⁻¹ :=
  sorry

/-- Direct image along `toSmallEtale X` is the composite `ε_{X,*} ⋙ π_{X,*}`. -/
@[simp]
theorem toSmallEtale_pushforward (X : Scheme.{u}) :
    (toSmallEtale X).pushforward =
      (standardComparison .etale X).pushforward ⋙ (siteMorphismOfTopoi X).pushforward :=
  sorry

/-- Inverse image along `a_S` is sheaf pullback along étale-to-ph relocalization. -/
noncomputable def toSmallEtaleInverseImageIso (S : Scheme.{u}) :
    (toSmallEtale S)⁻¹ ≅
      (relocalizationFunctor (𝟙 S)).sheafPullback (Type (u + 1))
        S.smallEtaleTopology (Scheme.bigPhSite S) :=
  let adjπ := (siteMorphismOfTopoi S).adjunction
  let adjε := (standardComparison .etale S).adjunction
  let adjA :=
    (relocalizationFunctor (𝟙 S)).sheafAdjunctionContinuous (Type (u + 1))
      S.smallEtaleTopology (Scheme.bigPhSite S)
  Adjunction.leftAdjointCompIso adjπ adjε adjA
    (Functor.isoWhiskerRight
        (Functor.sheafPushforwardContinuousComp'
          (Functor.rightUnitor (𝟭 (Over S))) (Type (u + 1))
          (S.overGrothendieckTopology @Etale)
          (Scheme.fppfTopology.over S)
          (Scheme.bigPhSite S))
        (siteMorphismOfTopoi S).pushforward ≪≫
      Functor.sheafPushforwardContinuousComp'
        (Functor.rightUnitor (relocalizationFunctor (𝟙 S))) (Type (u + 1))
        S.smallEtaleTopology (S.overGrothendieckTopology @Etale)
        (Scheme.bigPhSite S))

end AlgebraicGeometry.Scheme.PhComparison

end

end
