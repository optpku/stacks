/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.AffineComparison
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

/-!
# Ringed-topos comparison for affine standard sites

This module equips the affine standard site with the canonical inverse image of
the big structure sheaf and records the bundled comparison with the big ringed
topos.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.StandardTopology.Affine

/-- The geometric morphism from the affine standard topos to the big `τ`-topos. -/
noncomputable def toBig (τ : StandardTopology) (S : Scheme.{u}) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (τ.overTopology S) (topology τ S) :=
  Functor.morphismOfTopoiInOfCocontinuous.{u + 1, u, u, u + 1, u + 1}
    (Scheme.AffineOver.forget S) (topology τ S) (τ.overTopology S)

/-- The inverse image of `toBig` is restriction along the affine inclusion. -/
theorem toBig_inverseImage (τ : StandardTopology) (S : Scheme.{u}) :
    (toBig τ S).inverseImage =
      (Scheme.AffineOver.forget S).sheafPushforwardContinuous (Type (u + 1))
        (topology τ S) (τ.overTopology S) := sorry

/-- The affine structure sheaf is the canonical ring-valued inverse image of the lifted big
structure sheaf. -/
noncomputable def structureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    Sheaf (topology τ S) RingCat.{u + 1} :=
  (toBig τ S).ringInverseImage.obj
    (StandardTopology.Big.liftedStructureSheaf τ S)

/-- The canonical affine structure sheaf agrees with restriction of the lifted big structure
sheaf along the affine inclusion. -/
theorem structureSheaf_eq_restriction (τ : StandardTopology) (S : Scheme.{u}) :
    structureSheaf τ S =
      ((Scheme.AffineOver.forget S).sheafPushforwardContinuous RingCat.{u + 1}
          (topology τ S) (τ.overTopology S)).obj
          (StandardTopology.Big.liftedStructureSheaf τ S) := sorry

/-- On an affine object, the canonical affine structure sheaf is its lifted ring of global
functions. -/
theorem structureSheaf_obj (τ : StandardTopology) (S : Scheme.{u}) (U : S.AffineOver) :
    (structureSheaf τ S).obj.obj (op U) =
      Scheme.Site.ringUniverseLiftObj.{u, u + 1}
        (RingCat.of Γ((Scheme.AffineOver.toScheme S).obj U, ⊤)) := sorry

/-- Restriction maps in the canonical affine structure sheaf are induced by pullback of
functions. -/
theorem structureSheaf_map (τ : StandardTopology) (S : Scheme.{u})
    {U V : S.AffineOver} (f : U ⟶ V) :
    eqToHom (structureSheaf_obj τ S V).symm ≫
        (structureSheaf τ S).obj.map f.op ≫
      eqToHom (structureSheaf_obj τ S U) =
      Scheme.Site.ringUniverseLiftMap.{u, u + 1}
        (RingCat.ofHom ((Scheme.AffineOver.toScheme S).map f).appTop.hom) := sorry

/-- The affine standard site equipped with its canonical inverse-image structure sheaf. -/
abbrev ringedSite (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (topology τ S) (structureSheaf τ S)

/-- The affine ringed site's structure sheaf is the canonical inverse image of the big
structure sheaf. -/
theorem ringedSite_structureSheaf (τ : StandardTopology) (S : Scheme.{u}) :
    (ringedSite τ S).structureSheaf = structureSheaf τ S := sorry

/-- The canonical comparison from the affine standard ringed topos to the big standard
ringed topos. -/
noncomputable def comparison (τ : StandardTopology) (S : Scheme.{u}) :
    RingedSite.ToposHom (ringedSite τ S)
      (StandardTopology.Big.liftedRingedSite τ S) where
  toTopos := toBig τ S
  structureMap := 𝟙 (structureSheaf τ S)

/-- The underlying topos morphism of the ringed comparison is the affine-to-big comparison. -/
theorem comparison_toTopos (τ : StandardTopology) (S : Scheme.{u}) :
    (comparison τ S).toTopos = toBig τ S := sorry

/-- The structure map of the affine standard comparison is the identity of its canonical
inverse-image structure sheaf. -/
theorem comparison_structureMap (τ : StandardTopology) (S : Scheme.{u}) :
    (comparison τ S).structureMap = 𝟙 (structureSheaf τ S) := sorry

/-- The inverse image of the affine standard comparison is restriction along the affine
inclusion. -/
theorem comparison_inverseImage (τ : StandardTopology) (S : Scheme.{u}) :
    (comparison τ S).toTopos.inverseImage =
      (Scheme.AffineOver.forget S).sheafPushforwardContinuous (Type (u + 1))
        (topology τ S) (τ.overTopology S) := sorry

/-- The affine standard comparison is canonically an equivalence of ringed topoi. -/
instance comparison_isEquivalence (τ : StandardTopology) (S : Scheme.{u}) :
    (comparison τ S).IsEquivalence := sorry

end AlgebraicGeometry.StandardTopology.Affine
