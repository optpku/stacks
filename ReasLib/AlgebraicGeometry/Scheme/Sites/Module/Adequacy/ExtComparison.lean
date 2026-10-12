/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Adequacy.Property

@[expose] public section

open CategoryTheory Opposite Limits
open AlgebraicGeometry

noncomputable section

universe w u

namespace SheafOfModules.Adeq

/-- For an affine scheme, the inclusion of adequate module sheaves into all module sheaves
induces an isomorphism on `Ext` in every nonnegative degree. -/
theorem mapExtAddHom_isIso
    (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [ObjectProperty.IsWeakSerreClass (property (Scheme.Spec.obj (op A)) τ)]
    [HasExt.{w} (property (Scheme.Spec.obj (op A)) τ).FullSubcategory]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    (ℱ 𝒢 : (property (Scheme.Spec.obj (op A)) τ).FullSubcategory) (i : ℕ) :
    IsIso (AddCommGrpCat.ofHom
      ((property (Scheme.Spec.obj (op A)) τ).ι.mapExtAddHom ℱ 𝒢 i)) := sorry

/-- The map on `Ext` induced by including adequate module sheaves into all module sheaves is
bijective on an affine scheme. -/
theorem mapExtAddHom_bijective
    (τ : StandardTopology) (A : CommRingCat.{u})
    [Abelian (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    [ObjectProperty.IsWeakSerreClass (property (Scheme.Spec.obj (op A)) τ)]
    [HasExt.{w} (property (Scheme.Spec.obj (op A)) τ).FullSubcategory]
    [HasExt.{w} (RingedSite.ModuleCat.{u}
      (StandardTopology.Big.ringedSite τ (Scheme.Spec.obj (op A))))]
    (ℱ 𝒢 : (property (Scheme.Spec.obj (op A)) τ).FullSubcategory) (i : ℕ) :
    Function.Bijective
      ((property (Scheme.Spec.obj (op A)) τ).ι.mapExtAddHom ℱ 𝒢 i) := sorry

end SheafOfModules.Adeq
