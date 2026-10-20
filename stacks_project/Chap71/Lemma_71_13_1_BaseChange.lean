/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap65.Lemma_65_12_3_Pullback
public import stacks_project.Chap71.Lemma_71_11_5_Pointwise
public import stacks_project.Chap71.Lemma_71_11_5_TwistBaseChange
public import stacks_project.Chap71.Lemma_71_13_1_Canonical

/-!
# Base change of invertible maps into relative Proj

Pullback of `L`, `ψ`, and `U(ψ)` along a morphism `X' ⟶ X`, and comparison of the
canonical morphism with the fibre product of relative Proj via
`canonicalBaseChangeIso`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : X ⟶ Y)
variable {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y)}
variable (deg : DegreePieces 𝒜) (L : X.Modules)
variable [isInvertibleObject L] (ψ : GradedMapToPowers f deg L)

/-- Tensor powers of the pullback of an invertible module. -/
def pullbackPowers {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    X'.Modules :=
  tensorPowerUnit ((Modules.pullback g').obj L) n

/-- `pullbackPowers g' n` is the unit-based tensor power of `g'^* L`. -/
theorem pullbackPowers_eq {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    pullbackPowers L g' n = tensorPowerUnit ((Modules.pullback g').obj L) n :=
  rfl

/-- The pullback of a graded map into tensor powers along `g' : X' ⟶ X`. -/
def pullbackHom {X' : AlgebraicSpace S} (g' : X' ⟶ X) :
    GradedMapToPowers (g' ≫ f) deg ((Modules.pullback g').obj L) where
  hom n :=
    (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
      (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n
  map_one := sorry
  map_mul := sorry

/-- Homogeneous components of `pullbackHom` are composite-pullback comparison, then `ψ`,
then the tensor-power comparison. -/
theorem pullbackHom_hom {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    (pullbackHom f deg L ψ g').hom n =
      (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
        (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n :=
  sorry

/-- The inverse-image open `(g')^{-1}(U(ψ)) ⊂ X'`. -/
def domainInverseImage {X' : AlgebraicSpace S} (g' : X' ⟶ X) : OpenSubspace X' where
  X := pullback (domain f deg L ψ).ι g'
  ι := pullback.snd (domain f deg L ψ).ι g'
  isOpenImmersion := sorry

/-- The inclusion of `domainInverseImage` is the second projection of the pullback of
`U(ψ) ⊂ X` along `g'`. -/
theorem domainInverseImage_ι {X' : AlgebraicSpace S} (g' : X' ⟶ X) :
    (domainInverseImage f deg L ψ g').ι =
      pullback.snd (domain f deg L ψ).ι g' :=
  sorry

/-- Homogeneous component of the pullback of `ψ` along a commutative square, after
transport through an `AlgebraPullback` identification `𝒜' ≅ g^* 𝒜`. -/
def pullbackHomAlongSquareHom
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) (n : ℕ) :
    (Modules.pullback f').obj (deg'.obj n) ⟶
      tensorPowerUnit ((Modules.pullback g').obj L) n :=
  (Modules.pullback f').map (hAlg.degreeIso n).inv ≫
    (Modules.pullbackCompIso f' g).hom.app (deg.obj n) ≫
      eqToHom (congrArg (fun h ↦ (Modules.pullback h).obj (deg.obj n)) hf.symm) ≫
        (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
          (Modules.pullback g').map (ψ.hom n) ≫
            pullbackTensorPowerHom g' L n

/-- Homogeneous components of `pullbackHomAlongSquareHom` are algebra-pullback inverse,
then composite-pullback comparison, then `ψ`, then the tensor-power comparison. -/
theorem pullbackHomAlongSquareHom_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) (n : ℕ) :
    pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf n =
      (Modules.pullback f').map (hAlg.degreeIso n).inv ≫
        (Modules.pullbackCompIso f' g).hom.app (deg.obj n) ≫
          eqToHom (congrArg (fun h ↦ (Modules.pullback h).obj (deg.obj n)) hf.symm) ≫
            (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
              (Modules.pullback g').map (ψ.hom n) ≫
                pullbackTensorPowerHom g' L n :=
  sorry

/-- The pullback of `ψ` along a commutative square, transported through an
`AlgebraPullback` identification `𝒜' ≅ g^* 𝒜`. -/
def pullbackHomAlongSquare
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    GradedMapToPowers f' deg' ((Modules.pullback g').obj L) where
  hom := pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf
  map_one := sorry
  map_mul := sorry

/-- Homogeneous components of `pullbackHomAlongSquare` are `pullbackHomAlongSquareHom`. -/
theorem pullbackHomAlongSquare_hom
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) (n : ℕ) :
    (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf).hom n =
      pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf n :=
  sorry

variable {F : ProjFunctor Y 𝒜} (hF : F.IsAssociatedToQuadruples deg)

/-- The mediating morphism `(g')^{-1}(U(ψ)) ⟶ Y' ×_Y underline{Proj}_Y(𝒜)`. -/
def baseChangeToFibre
    {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    (domainInverseImage f deg L ψ g').X ⟶ fibreProduct g hF :=
  pullbackLift g (toAlgebraicSpace_hom F hF)
    (pullback.snd (domain f deg L ψ).ι g' ≫ f')
    (pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ)
    sorry

/-- The base change of `r_{L,ψ}` along the square, compared with relative Proj of `𝒜'`
via `canonicalBaseChangeIso`. -/
def baseChangeMap
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {F' : ProjFunctor Y' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    (domainInverseImage f deg L ψ g').X ⟶ toAlgebraicSpace F' hF' :=
  baseChangeToFibre f deg L ψ hF g g' f' ≫
    (canonicalBaseChangeIso g hAlg hF hF').inv

/-- `baseChangeMap` is the fibre-product lift followed by the inverse of
`canonicalBaseChangeIso`. -/
theorem baseChangeMap_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {F' : ProjFunctor Y' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    baseChangeMap f deg L ψ hF g hAlg hF' g' f' =
      baseChangeToFibre f deg L ψ hF g g' f' ≫
        (canonicalBaseChangeIso g hAlg hF hF').inv :=
  sorry

/-- Pullback of `θ_n` along the first projection of `(g')^{-1}(U(ψ))`, reassociated
onto the inverse-image inclusion. -/
def thetaAlongInverseImage
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    (Modules.pullback
        (pullback.fst (domain f deg L ψ).ι g' ≫
          canonicalMap f deg hF L ψ)).obj
        (CanonicalTwists.obj F hF (Int.ofNat n)) ⟶
      (Modules.pullback (domainInverseImage f deg L ψ g').ι).obj
        (tensorPowerUnit ((Modules.pullback g').obj L) n) :=
  (Modules.pullbackCompIso
        (pullback.fst (domain f deg L ψ).ι g')
        (canonicalMap f deg hF L ψ)).inv.app
      (CanonicalTwists.obj F hF (Int.ofNat n)) ≫
    (Modules.pullback (pullback.fst (domain f deg L ψ).ι g')).map
      (theta f deg hF L ψ n) ≫
      (Modules.pullbackCompIso
          (pullback.fst (domain f deg L ψ).ι g')
          (domain f deg L ψ).ι).hom.app
        (tensorPowerUnit L n) ≫
        eqToHom
            (congrArg
              (fun h ↦ (Modules.pullback h).obj (tensorPowerUnit L n))
              pullback.condition) ≫
          (Modules.pullbackCompIso
              (pullback.snd (domain f deg L ψ).ι g') g').inv.app
            (tensorPowerUnit L n) ≫
            (Modules.pullback (pullback.snd (domain f deg L ψ).ι g')).map
              (pullbackTensorPowerHom g' L n)

/-- Degreewise pullback of `θ` along the inverse-image inclusion, compared with the
canonical twists of the pulled-back relative Proj. -/
def baseChangeTheta
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {F' : ProjFunctor Y' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (n : ℕ) :
    (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).obj
        (CanonicalTwists.obj F' hF' (Int.ofNat n)) ⟶
      (Modules.pullback
          (baseChangeMap f deg L ψ hF g hAlg hF' g' f' ≫
            CanonicalTwists.BaseChange.map g hAlg hF hF')).obj
        (CanonicalTwists.obj F hF (Int.ofNat n)) :=
  (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).map
      (CanonicalTwists.BaseChange.degreeIso g hAlg hF hF' (Int.ofNat n)).inv ≫
    (Modules.pullbackCompIso
          (baseChangeMap f deg L ψ hF g hAlg hF' g' f')
          (CanonicalTwists.BaseChange.map g hAlg hF hF')).hom.app
      (CanonicalTwists.obj F hF (Int.ofNat n))


/-- `baseChangeTheta` is `degreeIso.inv` pulled back along `baseChangeMap`, reassociated
along `CanonicalTwists.BaseChange.map`. -/
theorem baseChangeTheta_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {F' : ProjFunctor Y' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (n : ℕ) :
    baseChangeTheta f deg L ψ hF g hAlg hF' g' f' n =
      (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).map
          (CanonicalTwists.BaseChange.degreeIso g hAlg hF hF' (Int.ofNat n)).inv ≫
        (Modules.pullbackCompIso
              (baseChangeMap f deg L ψ hF g hAlg hF' g' f')
              (CanonicalTwists.BaseChange.map g hAlg hF hF')).hom.app
          (CanonicalTwists.obj F hF (Int.ofNat n)) :=
  sorry

/-- The second projection of `baseChangeToFibre` recovers `r_{L,ψ}` along the first
projection of `(g')^{-1}(U(ψ))`. -/
theorem baseChangeToFibre_snd
    {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    baseChangeToFibre f deg L ψ hF g g' f' ≫ fibreProduct_snd g hF =
      pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ :=
  sorry

/-- `thetaAlongInverseImage` is the reassociated pullback of `θ` along the first
projection of `(g')^{-1}(U(ψ))`. -/
theorem thetaAlongInverseImage_eq
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    thetaAlongInverseImage f deg L ψ hF g' n =
      (Modules.pullbackCompIso
            (pullback.fst (domain f deg L ψ).ι g')
            (canonicalMap f deg hF L ψ)).inv.app
          (CanonicalTwists.obj F hF (Int.ofNat n)) ≫
        (Modules.pullback (pullback.fst (domain f deg L ψ).ι g')).map
          (theta f deg hF L ψ n) ≫
          (Modules.pullbackCompIso
              (pullback.fst (domain f deg L ψ).ι g')
              (domain f deg L ψ).ι).hom.app
            (tensorPowerUnit L n) ≫
            eqToHom
                (congrArg
                  (fun h ↦ (Modules.pullback h).obj (tensorPowerUnit L n))
                  pullback.condition) ≫
              (Modules.pullbackCompIso
                  (pullback.snd (domain f deg L ψ).ι g') g').inv.app
                (tensorPowerUnit L n) ≫
                (Modules.pullback (pullback.snd (domain f deg L ψ).ι g')).map
                  (pullbackTensorPowerHom g' L n) :=
  sorry

/-- Formation of `U(ψ)` commutes with pullback along any morphism `X' ⟶ X`. -/
theorem domain_pullback {X' : AlgebraicSpace S} (g' : X' ⟶ X)
    [isInvertibleObject ((Modules.pullback g').obj L)]
    {T : Over S} (w' : ofOver T ⟶ X') :
    memDomain f deg L ψ (w' ≫ g') ↔
      memDomain (g' ≫ f) deg ((Modules.pullback g').obj L)
        (pullbackHom f deg L ψ g') w' :=
  sorry

/-- Membership in `U(ψ')` for a scheme test of the square is membership of the
composite test in `U(ψ)`. -/
theorem memDomain_square
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)]
    {T : Over S} (w' : ofOver T ⟶ X') :
    memDomain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf) w' ↔
      memDomain f deg L ψ (w' ≫ g') :=
  sorry


/-- A scheme test of `U(ψ')` and the original classified map of the composite test form a
cone over `g` and `π`. -/
theorem classifiedMap_fibre_w
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)]
    {T : Over S} (w' : ofOver T ⟶ X')
    (hw : memDomain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf) w') :
    (w' ≫ f') ≫ g =
      classifiedMap f deg hF L ψ (w' ≫ g')
          ((memDomain_square f deg L ψ g hAlg g' f' hf w').mp hw) ≫
        toAlgebraicSpace_hom F hF :=
  sorry

/-- Restriction of `g'` along the canonical opens, as a morphism
`U(ψ') ⟶ U(ψ)`. -/
def domainRestrictAlong
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.X ⟶
      (domain f deg L ψ).X where
  app T :=
    TypeCat.ofHom fun
      (x :
        (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T) ↦
        ⟨g'.app T x.1, sorry⟩
  naturality := sorry

/-- Restriction of `g'` to the canonical opens lies over `X`. -/
theorem domainRestrictAlong_comp
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf ≫
        (domain f deg L ψ).ι =
      (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι ≫
        g' :=
  sorry

/-- The inverse-image inclusion factors through `U(ψ')`. -/
def domainBaseChangeInv
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (domainInverseImage f deg L ψ g').X ⟶
      (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.X where
  app T :=
    TypeCat.ofHom fun p ↦
      ⟨(domainInverseImage f deg L ψ g').ι.app T p, sorry⟩
  naturality := sorry

/-- The inverse of `domainBaseChangeIso` lies over `X'`. -/
theorem domainBaseChangeInv_comp
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    domainBaseChangeInv f deg L ψ g hAlg hF' g' f' hf ≫
        (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι =
      (domainInverseImage f deg L ψ g').ι :=
  sorry

/-- Identification `U(ψ') ≅ (g')^{-1}(U(ψ))` of algebraic spaces over `X'`. -/
def domainBaseChangeIso
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.X ≅
      (domainInverseImage f deg L ψ g').X where
  hom :=
    pullback.lift
      (domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf)
      (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι
      (domainRestrictAlong_comp f deg L ψ g hAlg hF' g' f' hf)
  inv := domainBaseChangeInv f deg L ψ g hAlg hF' g' f' hf
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identification `U(ψ') ≅ (g')^{-1}(U(ψ))` lies over `X'`. -/
theorem domainBaseChangeIso_ι
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        (domainInverseImage f deg L ψ g').ι =
      (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι :=
  sorry

/-- The forward map of `domainBaseChangeIso` is the pullback lift of the restricted
`g'` and the inclusion of `U(ψ')`. -/
theorem domainBaseChangeIso_hom
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom =
      pullback.lift
        (domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf)
        (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι
        (domainRestrictAlong_comp f deg L ψ g hAlg hF' g' f' hf) :=
  sorry

/-- The canonical morphism of the pulled-back data is the domain identification
followed by `baseChangeMap`. -/
theorem canonicalMap_eq_baseChangeMap
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).map =
      (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        baseChangeMap f deg L ψ hF g hAlg hF' g' f' :=
  sorry

/-- After composing with `canonicalBaseChangeIso`, the canonical morphism of the
pulled-back data is the fibre-product lift of `r_{L,ψ}`. -/
theorem canonicalMap_comp_fibre
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).map ≫
        (canonicalBaseChangeIso g hAlg hF hF').hom =
      (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        baseChangeToFibre f deg L ψ hF g g' f' :=
  sorry

/-- `baseChangeMap` followed by the twist base-change morphism recovers the
restriction of `r_{L,ψ}` along the first projection of `(g')^{-1}(U(ψ))`. -/
theorem baseChangeMap_comp_twists
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') :
    baseChangeMap f deg L ψ hF g hAlg hF' g' f' ≫
        CanonicalTwists.BaseChange.map g hAlg hF hF' =
      pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ :=
  sorry

/-- Pullback of `θ` along `(g')^{-1}(U(ψ))`, transported to the canonical twists of
relative Proj of `𝒜'` by `CanonicalTwists.BaseChange.degreeIso`. -/
def thetaBaseChange
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (n : ℕ) :
    (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).obj
        (CanonicalTwists.obj F' hF' (Int.ofNat n)) ⟶
      (Modules.pullback (domainInverseImage f deg L ψ g').ι).obj
        (tensorPowerUnit ((Modules.pullback g').obj L) n) :=
  (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).map
      (CanonicalTwists.BaseChange.degreeIso g hAlg hF hF' (Int.ofNat n)).inv ≫
    (Modules.pullbackCompIso
          (baseChangeMap f deg L ψ hF g hAlg hF' g' f')
          (CanonicalTwists.BaseChange.map g hAlg hF hF')).hom.app
      (CanonicalTwists.obj F hF (Int.ofNat n)) ≫
      eqToHom
          (congrArg
            (fun h ↦
              (Modules.pullback h).obj (CanonicalTwists.obj F hF (Int.ofNat n)))
            (baseChangeMap_comp_twists f deg L ψ hF g hAlg hF' g' f')) ≫
        thetaAlongInverseImage f deg L ψ hF g' n

/-- `thetaBaseChange` is `degreeIso.inv` pulled back along `baseChangeMap`,
reassociated, then `thetaAlongInverseImage`. -/
theorem thetaBaseChange_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (n : ℕ) :
    thetaBaseChange f deg L ψ hF g hAlg hF' g' f' n =
      (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).map
          (CanonicalTwists.BaseChange.degreeIso g hAlg hF hF' (Int.ofNat n)).inv ≫
        (Modules.pullbackCompIso
              (baseChangeMap f deg L ψ hF g hAlg hF' g' f')
              (CanonicalTwists.BaseChange.map g hAlg hF hF')).hom.app
          (CanonicalTwists.obj F hF (Int.ofNat n)) ≫
          eqToHom
              (congrArg
                (fun h ↦
                  (Modules.pullback h).obj
                    (CanonicalTwists.obj F hF (Int.ofNat n)))
                (baseChangeMap_comp_twists f deg L ψ hF g hAlg hF' g' f')) ≫
            thetaAlongInverseImage f deg L ψ hF g' n :=
  sorry

/-- Transport of `thetaBaseChange` along `domainBaseChangeIso`, as a map
`r'^* 𝒪'(n) ⟶ (L')^{⊗ n}|_{U(ψ')}`. -/
def thetaCanonicalBaseChange
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] (n : ℕ) :
    (Modules.pullback
        (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).map).obj
        (CanonicalTwists.obj F' hF' (Int.ofNat n)) ⟶
      (Modules.pullback
          (SectionMap.canonical f' deg' hF' ((Modules.pullback g').obj L)
              (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).domain.ι).obj
        (tensorPowerUnit ((Modules.pullback g').obj L) n) :=
  eqToHom
      (congrArg
        (fun h ↦
          (Modules.pullback h).obj (CanonicalTwists.obj F' hF' (Int.ofNat n)))
        (canonicalMap_eq_baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)) ≫
    (Modules.pullbackCompIso
          (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
          (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).inv.app
      (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
      (Modules.pullback
            (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom).map
        (thetaBaseChange f deg L ψ hF g hAlg hF' g' f' n) ≫
        (Modules.pullbackCompIso
              (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
              (domainInverseImage f deg L ψ g').ι).hom.app
          (tensorPowerUnit ((Modules.pullback g').obj L) n) ≫
          eqToHom
            (congrArg
              (fun h ↦
                (Modules.pullback h).obj
                  (tensorPowerUnit ((Modules.pullback g').obj L) n))
              (domainBaseChangeIso_ι f deg L ψ g hAlg hF' g' f' hf))

/-- `thetaCanonicalBaseChange` is the transport of `thetaBaseChange` along
`domainBaseChangeIso`. -/
theorem thetaCanonicalBaseChange_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] (n : ℕ) :
    thetaCanonicalBaseChange f deg L ψ hF g hAlg hF' g' f' hf n =
      eqToHom
          (congrArg
            (fun h ↦
              (Modules.pullback h).obj
                (CanonicalTwists.obj F' hF' (Int.ofNat n)))
            (canonicalMap_eq_baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)) ≫
        (Modules.pullbackCompIso
              (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
              (baseChangeMap f deg L ψ hF g hAlg hF' g' f')).inv.app
          (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
          (Modules.pullback
                (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom).map
            (thetaBaseChange f deg L ψ hF g hAlg hF' g' f' n) ≫
            (Modules.pullbackCompIso
                  (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
                  (domainInverseImage f deg L ψ g').ι).hom.app
              (tensorPowerUnit ((Modules.pullback g').obj L) n) ≫
              eqToHom
                (congrArg
                  (fun h ↦
                    (Modules.pullback h).obj
                      (tensorPowerUnit ((Modules.pullback g').obj L) n))
                  (domainBaseChangeIso_ι f deg L ψ g hAlg hF' g' f' hf)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
