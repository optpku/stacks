/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Representability
public import stacks_project.Chap67.Example_67_53_3_Homeomorphism
public import stacks_project.Chap72.Example_72_6_11_Relation

/-!
# The coordinate-axes quotient algebraic space

This module records the fppf sheaf quotient `X = U / R` of the coordinate axes by the
étale equivalence relation of `Example_72_6_11_Relation`, together with the descended
morphism `X ⟶ 𝔸¹_k` induced by `(x, y) ↦ x + y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution (isUniversalHomeomorphism)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient

/-- The fppf sheaf `X = U / R`, obtained by sheafifying the universe-raised quotient presheaf. -/
def sheafOfPoints (k : Type u) [Field k] :
    Sheaf (Scheme.fppfTopology.over (base k)) (Type (u + 1)) :=
  (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k))

/-- `sheafOfPoints k` is the fppf quotient sheaf of the coordinate-axes pre-relation. -/
theorem sheafOfPoints_eq (k : Type u) [Field k] :
    sheafOfPoints k = (preRelation k).quotientSheaf (Scheme.fppfTopology.over (base k)) := sorry

/-- The atlas `U ⟶ X` as a morphism of fppf sheaves, given by the canonical quotient map. -/
def atlas (k : Type u) [Field k] :
    (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (cover k) ⟶ sheafOfPoints k :=
  (preRelation k).quotientMap (Scheme.fppfTopology.over (base k))

/-- The atlas is the canonical fppf quotient map of the pre-relation. -/
theorem atlas_eq (k : Type u) [Field k] :
    atlas k = (preRelation k).quotientMap (Scheme.fppfTopology.over (base k)) := sorry

/-- The fppf quotient sheaf `X = U / R` is an algebraic space over `Spec k`: it has a
representable étale locally-surjective atlas from `U` and a representable diagonal. -/
theorem sheafOfPoints_spec (k : Type u) [Field k] :
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} (atlas k).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (base k)) (atlas k).hom ∧
        uliftYoneda.{u + 1}.relativelyRepresentable (diag (sheafOfPoints k).obj) := sorry

/-- The diagonal of `X = U / R` is quasi-compact relative to `uliftYoneda`, so `X` is
quasi-separated. -/
theorem quasiCompact_diag_sheafOfPoints (k : Type u) [Field k] :
    (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
      (diag (sheafOfPoints k).obj) := sorry

/-- The affine line `𝔸¹_k` as a scheme over `Spec k`. -/
def affineLine (k : Type u) [Field k] : Over (base k) :=
  Over.mk (affineSpaceOverFieldHom k 1)

/-- The underlying scheme of `affineLine` is affine 1-space over `k`. -/
theorem affineLine_left (k : Type u) [Field k] :
    (affineLine k).left = AffineSpaceOverField k 1 := sorry

/-- The structure morphism of `affineLine` is the canonical map `𝔸¹_k ⟶ Spec k`. -/
theorem affineLine_hom (k : Type u) [Field k] :
    (affineLine k).hom = affineSpaceOverFieldHom k 1 := sorry

/-- The unique coordinate function on `𝔸¹_k`. -/
def affineLineCoord (k : Type u) [Field k] : Γ((affineLine k).left, ⊤) :=
  AffineSpace.coord (base k) (ULift.up (0 : Fin 1))

/-- `affineLineCoord` is the standard coordinate of `𝔸¹_k`. -/
theorem affineLineCoord_eq (k : Type u) [Field k] :
    affineLineCoord k = AffineSpace.coord (base k) (ULift.up (0 : Fin 1)) := sorry

/-- The basic open `D(t) ⊆ 𝔸¹_k`. -/
def puncturedAffineLineOpen (k : Type u) [Field k] : (affineLine k).left.Opens :=
  (affineLine k).left.basicOpen (affineLineCoord k)

/-- The punctured affine line is the basic open of the unique coordinate. -/
theorem puncturedAffineLineOpen_eq (k : Type u) [Field k] :
    puncturedAffineLineOpen k = (affineLine k).left.basicOpen (affineLineCoord k) := sorry

/-- The open `𝔸¹_k \ {0}` as a scheme over `Spec k`. -/
def puncturedAffineLineOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk ((puncturedAffineLineOpen k).ι ≫ (affineLine k).hom)

/-- The structure morphism of `puncturedAffineLineOver` is the open immersion followed by
the structure map of the affine line. -/
theorem puncturedAffineLineOver_hom (k : Type u) [Field k] :
    (puncturedAffineLineOver k).hom =
      (puncturedAffineLineOpen k).ι ≫ (affineLine k).hom := sorry

/-- The open immersion `𝔸¹_k \ {0} ⟶ 𝔸¹_k` as a morphism over `Spec k`. -/
def puncturedAffineLineι (k : Type u) [Field k] : puncturedAffineLineOver k ⟶ affineLine k :=
  Over.homMk (puncturedAffineLineOpen k).ι

/-- The underlying scheme map of `puncturedAffineLineι` is the open immersion of `D(t)`. -/
theorem puncturedAffineLineι_left (k : Type u) [Field k] :
    (puncturedAffineLineι k).left = (puncturedAffineLineOpen k).ι := sorry

/-- The inclusion of `𝔸¹_k \ {0}` into the affine line is an open immersion. -/
instance instIsOpenImmersion_puncturedAffineLineι (k : Type u) [Field k] :
    IsOpenImmersion (puncturedAffineLineι k).left := sorry

/-- The origin of `𝔸¹_k`, viewed as a scheme over `Spec k`. -/
def affineLineOriginOver (k : Type u) [Field k] : Over (base k) :=
  Over.mk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) ≫ (affineLine k).hom)

/-- `affineLineOriginOver` is the zero section of the affine line, viewed in `Over (Spec k)`. -/
theorem affineLineOriginOver_eq (k : Type u) [Field k] :
    affineLineOriginOver k =
      Over.mk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) ≫ (affineLine k).hom) := sorry

/-- The origin morphism `Spec k ⟶ 𝔸¹_k` over `Spec k`. -/
def affineLineOriginToAffineLine (k : Type u) [Field k] :
    affineLineOriginOver k ⟶ affineLine k :=
  Over.homMk (AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k))

/-- The underlying scheme morphism of `affineLineOriginToAffineLine` is the zero section. -/
theorem affineLineOriginToAffineLine_left (k : Type u) [Field k] :
    (affineLineOriginToAffineLine k).left =
      AffineSpace.zeroLeft (ULift.{u} (Fin 1)) (base k) := sorry

/-- The morphism `U ⟶ 𝔸¹_k` given by `(x, y) ↦ x + y` commutes with the structure
morphisms to `Spec k`. -/
theorem sumOver_w (k : Type u) [Field k] :
    AffineSpace.homOfVector (cover k).hom (fun _ : ULift.{u} (Fin 1) ↦ sumSection k) ≫
        (affineLine k).hom = (cover k).hom := sorry

/-- The morphism `U ⟶ 𝔸¹_k` sending `(x, y)` to `x + y`. -/
def sumOver (k : Type u) [Field k] : cover k ⟶ affineLine k :=
  Over.homMk
    (AffineSpace.homOfVector (cover k).hom (fun _ : ULift.{u} (Fin 1) ↦ sumSection k))
    (sumOver_w k)

/-- The underlying scheme morphism of `sumOver` is `homOfVector` of the section `x + y`. -/
theorem sumOver_left (k : Type u) [Field k] :
    (sumOver k).left =
      AffineSpace.homOfVector (cover k).hom (fun _ : ULift.{u} (Fin 1) ↦ sumSection k) := sorry

/-- The sum map equalizes the two projections of the coordinate-axes relation. -/
theorem sumOver_equalizes (k : Type u) [Field k] :
    (preRelation k).t ≫ sumOver k = (preRelation k).s ≫ sumOver k := sorry

/-- The descended morphism `X ⟶ 𝔸¹_k` induced by `(x, y) ↦ x + y` on the atlas. -/
def toAffineLine (k : Type u) [Field k] :
    sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (affineLine k) :=
  (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
    (sumOver k) (sumOver_equalizes k)

/-- `toAffineLine` is the canonical quotient-sheaf descent of `sumOver`. -/
theorem toAffineLine_eq (k : Type u) [Field k] :
    toAffineLine k =
      (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
        (sumOver k) (sumOver_equalizes k) := sorry

/-- On the atlas, `toAffineLine` recovers the sum map `(x, y) ↦ x + y`. -/
theorem toAffineLine_comp_atlas (k : Type u) [Field k] :
    atlas k ≫ toAffineLine k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (sumOver k) := sorry

/-- `toAffineLine` is an isomorphism after base change along `𝔸¹_k \ {0} ⟶ 𝔸¹_k`. -/
theorem isIso_over_punctured (k : Type u) [Field k] :
    IsIso
      (pullback.snd (toAffineLine k)
        ((Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map
          (puncturedAffineLineι k))) :=
  sorry

/-- The morphism `X ⟶ 𝔸¹_k` is a universal homeomorphism in the sense of
Definition 67.53.2. -/
theorem universalHomeomorphism_toAffineLine (k : Type u) [Field k] :
    isUniversalHomeomorphism (toAffineLine k) := sorry

end AlgebraicGeometry.AlgebraicSpace.CoordinateAxesQuotient
