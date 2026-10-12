/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Affine.Quasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 35.11.1 (1): the affine scalar-extension comparisons are isomorphisms exactly when
the module presheaf is quasi-coherent for any selected standard topology. -/
@[stacks 0GZV] #check
  (AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.isCartesian_iff_isQuasicoherentFor :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf S),
      AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.IsCartesian F ↔
        AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.IsQuasicoherentFor F τ)

/- Lemma 35.11.1 (2): cartesian affine module presheaves are exactly those obtained by
restricting quasi-coherent modules from the corresponding big standard site. -/
@[stacks 0GZV] #check
  (AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.isCartesian_iff_essImage_big :
    ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
      (F : AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf S),
      AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.IsCartesian F ↔
        (AlgebraicGeometry.StandardTopology.Affine.bigRestriction τ S ⋙
          AlgebraicGeometry.StandardTopology.Affine.CartesianModule.inclusion S).essImage F)

/- Lemma 35.11.1 (3): cartesian affine module presheaves are exactly those coming from a
unique compatible quasi-coherent module on the base scheme. -/
@[stacks 0GZV] #check
  (AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.isCartesian_iff_hasUniqueSchemeModel :
    ∀ (S : AlgebraicGeometry.Scheme.{u})
      (F : AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf S),
      AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.IsCartesian F ↔
        AlgebraicGeometry.StandardTopology.Affine.ModulePresheaf.HasUniqueSchemeModel F)
