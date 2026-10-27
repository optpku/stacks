/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback.Equality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.CanonicalTwists.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.SectionMap
public import Mathlib.Tactic.DSimpPercent

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

/-- Pullback of the homogeneous components preserves the unit and multiplication laws. -/
theorem pullbackHom_laws {X' : AlgebraicSpace S} (g' : X' ⟶ X) :
    (Modules.structureModulePullbackInv (g' ≫ f) ≫
        (Modules.pullback (g' ≫ f)).map (degreeZeroUnit deg) ≫ (fun n ↦ (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
      (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n) 0 =
      eqToHom (tensorPowerUnit_zero ((Modules.pullback g').obj L)).symm) ∧
    (∀ i j : ℕ,
      pullbackTensorLax (g' ≫ f) (deg.obj i) (deg.obj j) ≫
          (Modules.pullback (g' ≫ f)).map (deg.mul i j) ≫ (fun n ↦ (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
      (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n) (i + j) =
        tensorHom ((fun n ↦ (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
      (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n) i) ((fun n ↦ (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
      (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n) j) ≫ (tensorPowerUnitAddIso ((Modules.pullback g').obj L) i j).hom) := sorry

/-- The pullback of a graded map into tensor powers along `g' : X' ⟶ X`. -/
def pullbackHom {X' : AlgebraicSpace S} (g' : X' ⟶ X) :
    GradedMapToPowers (g' ≫ f) deg ((Modules.pullback g').obj L) where
  hom n :=
    (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
      (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n
  map_one := (pullbackHom_laws f deg L ψ g').1
  map_mul := (pullbackHom_laws f deg L ψ g').2

/-- Homogeneous components of `pullbackHom` are composite-pullback comparison, then `ψ`,
then the tensor-power comparison. -/
theorem pullbackHom_hom {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    (pullbackHom f deg L ψ g').hom n =
      (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
        (Modules.pullback g').map (ψ.hom n) ≫ pullbackTensorPowerHom g' L n :=
  rfl

/-- The inverse-image open `(g')^{-1}(U(ψ)) ⊂ X'`. -/
def domainInverseImage {X' : AlgebraicSpace S} (g' : X' ⟶ X) : OpenSubspace X' where
  X := pullback (domain f deg L ψ).ι g'
  ι := pullback.snd (domain f deg L ψ).ι g'
  isOpenImmersion := IsOpenImmersion.pullback_snd (domain f deg L ψ).isOpenImmersion g'

/-- The inclusion of `domainInverseImage` is the second projection of the pullback of
`U(ψ) ⊂ X` along `g'`. -/
theorem domainInverseImage_ι {X' : AlgebraicSpace S} (g' : X' ⟶ X) :
    (domainInverseImage f deg L ψ g').ι =
      pullback.snd (domain f deg L ψ).ι g' :=
  rfl

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
      (Modules.pullbackCongr hf).inv.app (deg.obj n) ≫
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
      (Modules.pullbackCongr hf).inv.app (deg.obj n) ≫
        (Modules.pullbackCompIso g' f).inv.app (deg.obj n) ≫
          (Modules.pullback g').map (ψ.hom n) ≫
            pullbackTensorPowerHom g' L n :=
  rfl

/-- Pullback of the homogeneous components preserves the unit and multiplication laws. -/
theorem pullbackHomAlongSquare_laws
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    (Modules.structureModulePullbackInv f' ≫
        (Modules.pullback f').map (degreeZeroUnit deg') ≫ (pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf) 0 =
      eqToHom (tensorPowerUnit_zero ((Modules.pullback g').obj L)).symm) ∧
    (∀ i j : ℕ,
      pullbackTensorLax f' (deg'.obj i) (deg'.obj j) ≫
          (Modules.pullback f').map (deg'.mul i j) ≫ (pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf) (i + j) =
        tensorHom ((pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf) i) ((pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf) j) ≫ (tensorPowerUnitAddIso ((Modules.pullback g').obj L) i j).hom) := sorry

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
  map_one := (pullbackHomAlongSquare_laws f deg L ψ g hAlg g' f' hf).1
  map_mul := (pullbackHomAlongSquare_laws f deg L ψ g hAlg g' f' hf).2

/-- Homogeneous components of `pullbackHomAlongSquare` are `pullbackHomAlongSquareHom`. -/
theorem pullbackHomAlongSquare_hom
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) (n : ℕ) :
    (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf).hom n =
      pullbackHomAlongSquareHom f deg L ψ g hAlg g' f' hf n :=
  rfl

variable {F : ProjFunctor Y 𝒜} (hF : F.IsAssociatedToQuadruples deg)

/-- The mediating morphism `(g')^{-1}(U(ψ)) ⟶ Y' ×_Y underline{Proj}_Y(𝒜)`. -/
def baseChangeToFibre
    {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    (domainInverseImage f deg L ψ g').X ⟶ fibreProduct g hF :=
  ReasLibPullback.pullbackLift g (toAlgebraicSpace_hom F hF)
    (pullback.snd (domain f deg L ψ).ι g' ≫ f')
    (pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ)
    (by
      calc
        (pullback.snd (domain f deg L ψ).ι g' ≫ f') ≫ g =
            (pullback.snd (domain f deg L ψ).ι g' ≫ g') ≫ f := by
          rw [Category.assoc, ← hf, ← Category.assoc]
        _ = (pullback.fst (domain f deg L ψ).ι g' ≫ (domain f deg L ψ).ι) ≫ f :=
          congrArg (fun k ↦ k ≫ f) pullback.condition.symm
        _ = (pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ) ≫
            toAlgebraicSpace_hom F hF := by
          exact (Category.assoc _ _ _).trans
            ((congrArg (fun k ↦ pullback.fst (domain f deg L ψ).ι g' ≫ k)
              (canonicalMap_over_base f deg hF L ψ).symm).trans
              (Category.assoc _ _ _).symm))

/-- The base change of `r_{L,ψ}` along the square, compared with relative Proj of `𝒜'`
via `canonicalBaseChangeIso`. -/
def baseChangeMap
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {F' : ProjFunctor Y' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    (domainInverseImage f deg L ψ g').X ⟶ toAlgebraicSpace F' hF' :=
  baseChangeToFibre f deg L ψ hF g g' f' hf ≫
    (canonicalBaseChangeIso g hAlg hF hF').inv

/-- `baseChangeMap` is the fibre-product lift followed by the inverse of
`canonicalBaseChangeIso`. -/
theorem baseChangeMap_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    {F' : ProjFunctor Y' 𝒜'} (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf =
      baseChangeToFibre f deg L ψ hF g g' f' hf ≫
        (canonicalBaseChangeIso g hAlg hF hF').inv :=
  rfl

/-- Pullback of `θ_n` along the first projection of `(g')^{-1}(U(ψ))`, reassociated
onto the inverse-image inclusion. -/
def TwistComparison.alongInverseImage
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
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
      (theta.hom n) ≫
      (Modules.pullbackCompIso
          (pullback.fst (domain f deg L ψ).ι g')
          (domain f deg L ψ).ι).hom.app
        (tensorPowerUnit L n) ≫
        (Modules.pullbackCongr pullback.condition).hom.app (tensorPowerUnit L n) ≫
          (Modules.pullbackCompIso
              (pullback.snd (domain f deg L ψ).ι g') g').inv.app
            (tensorPowerUnit L n) ≫
            (Modules.pullback (pullback.snd (domain f deg L ψ).ι g')).map
              (pullbackTensorPowerHom g' L n)

/-- The second projection of `baseChangeToFibre` recovers `r_{L,ψ}` along the first
projection of `(g')^{-1}(U(ψ))`. -/
theorem baseChangeToFibre_snd
    {Y' : AlgebraicSpace S} (g : Y' ⟶ Y)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    baseChangeToFibre f deg L ψ hF g g' f' hf ≫ fibreProduct_snd g hF =
      pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ :=
  ReasLibPullback.pullbackLift_snd _ _ _ _ _

/-- `TwistComparison.alongInverseImage` is the reassociated pullback of `θ` along the first
projection of `(g')^{-1}(U(ψ))`. -/
theorem TwistComparison.alongInverseImage_eq
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (n : ℕ) :
    TwistComparison.alongInverseImage f deg L ψ hF theta g' n =
      (dsimp% only [TwistComparison.alongInverseImage] (TwistComparison.alongInverseImage f deg L ψ hF theta g' n)) :=
  rfl

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


/-- The restriction on points lands in the prescribed domain and is natural. -/
theorem domainRestrictAlong_laws
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    ∃ h : ∀ (T : (Over S)ᵒᵖ)
      (x : (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T),
      (g'.app T x.1) ∈ (domainSubfunctor f deg L ψ).obj T,
    ∀ (T T' : (Over S)ᵒᵖ) (k : T ⟶ T'),
      (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.map k ≫
        TypeCat.ofHom (fun (x : (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T') ↦
          (⟨g'.app T' x.1, h T' x⟩ : (domainSubfunctor f deg L ψ).toFunctor.obj T')) =
      TypeCat.ofHom (fun (x : (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T) ↦
          (⟨g'.app T x.1, h T x⟩ : (domainSubfunctor f deg L ψ).toFunctor.obj T)) ≫
        (domainSubfunctor f deg L ψ).toFunctor.map k := sorry

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
    (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).X ⟶
      (domain f deg L ψ).X where
  app T :=
    TypeCat.ofHom fun
      (x :
        (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
            (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T) ↦
        ⟨g'.app T x.1, (domainRestrictAlong_laws f deg L ψ g hAlg hF' g' f' hf).choose T x⟩
  naturality := (domainRestrictAlong_laws f deg L ψ g hAlg hF' g' f' hf).choose_spec

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
      (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι ≫
        g' :=
  sorry

/-- The restriction on points lands in the prescribed domain and is natural. -/
theorem domainBaseChangeInv_laws
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    ∃ h : ∀ (T : (Over S)ᵒᵖ) (p : (domainInverseImage f deg L ψ g').X.functorOfPoints.obj T),
      ((domainInverseImage f deg L ψ g').ι.app T p) ∈
        (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).obj T,
    ∀ (T T' : (Over S)ᵒᵖ) (k : T ⟶ T'),
      (domainInverseImage f deg L ψ g').X.functorOfPoints.map k ≫
        TypeCat.ofHom (fun (x : (domainInverseImage f deg L ψ g').X.functorOfPoints.obj T') ↦
          (⟨(domainInverseImage f deg L ψ g').ι.app T' x, h T' x⟩ : (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T')) =
      TypeCat.ofHom (fun (x : (domainInverseImage f deg L ψ g').X.functorOfPoints.obj T) ↦
          (⟨(domainInverseImage f deg L ψ g').ι.app T x, h T x⟩ : (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.obj T)) ≫
        (domainSubfunctor f' deg' ((Modules.pullback g').obj L)
          (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).toFunctor.map k := sorry

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
      (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).X where
  app T :=
    TypeCat.ofHom fun p ↦
      ⟨(domainInverseImage f deg L ψ g').ι.app T p, (domainBaseChangeInv_laws f deg L ψ g hAlg hF' g' f' hf).choose T p⟩
  naturality := (domainBaseChangeInv_laws f deg L ψ g hAlg hF' g' f' hf).choose_spec

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
        (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι =
      (domainInverseImage f deg L ψ g').ι :=
  sorry

/-- The two canonical domain maps are mutually inverse. -/
theorem domainBaseChangeIso_laws
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    (pullback.lift (C := AlgebraicSpace S)
      (domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf)
      (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι
      (domainRestrictAlong_comp f deg L ψ g hAlg hF' g' f' hf)) ≫ (domainBaseChangeInv f deg L ψ g hAlg hF' g' f' hf) = 𝟙 _ ∧
    (domainBaseChangeInv f deg L ψ g hAlg hF' g' f' hf) ≫ (pullback.lift (C := AlgebraicSpace S)
      (domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf)
      (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι
      (domainRestrictAlong_comp f deg L ψ g hAlg hF' g' f' hf)) = 𝟙 _ := sorry

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
    (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).X ≅
      (domainInverseImage f deg L ψ g').X where
  hom :=
    pullback.lift (C := AlgebraicSpace S)
      (domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf)
      (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι
      (domainRestrictAlong_comp f deg L ψ g hAlg hF' g' f' hf)
  inv := domainBaseChangeInv f deg L ψ g hAlg hF' g' f' hf
  hom_inv_id := (domainBaseChangeIso_laws f deg L ψ g hAlg hF' g' f' hf).1
  inv_hom_id := (domainBaseChangeIso_laws f deg L ψ g hAlg hF' g' f' hf).2

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
      (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι :=
  Limits.pullback.lift_snd (C := AlgebraicSpace S) _ _ _

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
      pullback.lift (C := AlgebraicSpace S)
        (domainRestrictAlong f deg L ψ g hAlg hF' g' f' hf)
        (domain f' deg' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι
        (domainRestrictAlong_comp f deg L ψ g hAlg hF' g' f' hf) :=
  rfl

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
    (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)) =
      (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf :=
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
    (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
        (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)) ≫
        (canonicalBaseChangeIso g hAlg hF hF').hom =
      (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom ≫
        baseChangeToFibre f deg L ψ hF g g' f' hf :=
  by
    rw [canonicalMap_eq_baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf]
    simp only [baseChangeMap, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `baseChangeMap` followed by the twist base-change morphism recovers the
restriction of `r_{L,ψ}` along the first projection of `(g')^{-1}(U(ψ))`. -/
theorem baseChangeMap_comp_twists
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g) :
    baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf ≫
        CanonicalTwists.BaseChange.map g hAlg hF hF' =
      pullback.fst (domain f deg L ψ).ι g' ≫ canonicalMap f deg hF L ψ :=
  sorry

/-- Pullback of `θ` along `(g')^{-1}(U(ψ))`, transported to the canonical twists of
relative Proj of `𝒜'` by `CanonicalTwists.BaseChange.degreeIso`. -/
def TwistComparison.baseChange
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (hf : g' ≫ f = f' ≫ g) (n : ℕ) :
    (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).obj
        (CanonicalTwists.obj F' hF' (Int.ofNat n)) ⟶
      (Modules.pullback (domainInverseImage f deg L ψ g').ι).obj
        (tensorPowerUnit ((Modules.pullback g').obj L) n) :=
  (Modules.pullback (baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).map
      (CanonicalTwists.BaseChange.degreeIso g hAlg hF hF' (Int.ofNat n)).inv ≫
    (Modules.pullbackCompIso
          (baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)
          (CanonicalTwists.BaseChange.map g hAlg hF hF')).hom.app
      (CanonicalTwists.obj F hF (Int.ofNat n)) ≫
      (Modules.pullbackCongr (baseChangeMap_comp_twists f deg L ψ hF g hAlg hF' g' f' hf)).hom.app (CanonicalTwists.obj F hF (Int.ofNat n)) ≫
        TwistComparison.alongInverseImage f deg L ψ hF theta g' n

/-- `TwistComparison.baseChange` is `degreeIso.inv` pulled back along `baseChangeMap`,
reassociated, then `TwistComparison.alongInverseImage`. -/
theorem TwistComparison.baseChange_eq
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (hf : g' ≫ f = f' ≫ g) (n : ℕ) :
    TwistComparison.baseChange f deg L ψ hF g hAlg hF' theta g' f' hf n =
      (dsimp% only [TwistComparison.baseChange] (TwistComparison.baseChange f deg L ψ hF g hAlg hF' theta g' f' hf n)) :=
  rfl

/-- Transport along the square preserves the unit and homogeneous multiplication. -/
theorem TwistComparison.pullbackAlongSquare_laws
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    let component := fun n : ℕ ↦
      (Modules.pullbackCongr (canonicalMap_eq_baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).hom.app (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
        (Modules.pullbackCompIso
              (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
              (baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).inv.app
          (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
          (Modules.pullback
                (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom).map
            (TwistComparison.baseChange f deg L ψ hF g hAlg hF' theta g' f' hf n) ≫
            (Modules.pullbackCompIso
                  (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
                  (domainInverseImage f deg L ψ g').ι).hom.app
              (tensorPowerUnit ((Modules.pullback g').obj L) n) ≫
              (Modules.pullbackCongr (domainBaseChangeIso_ι f deg L ψ g hAlg hF' g' f' hf)).hom.app (tensorPowerUnit ((Modules.pullback g').obj L) n)
    ((Modules.pullback (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))).map (CanonicalTwists.unit F' hF') ≫ component 0 =
      (pullbackMonoidalUnitIso (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))).hom ≫
        Modules.structureModulePullbackInv (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι ≫
          (Modules.pullback (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι).map (eqToHom (tensorPowerUnit_zero ((Modules.pullback g').obj L)).symm)) ∧
    (∀ i j : ℕ,
      pullbackTensorLax (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))
            (CanonicalTwists.obj F' hF' (Int.ofNat i))
            (CanonicalTwists.obj F' hF' (Int.ofNat j)) ≫
          (Modules.pullback (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))).map
              (CanonicalTwists.mul F' hF' (Int.ofNat i) (Int.ofNat j)) ≫
            eqToHom
                (congrArg
                  (fun k : ℤ ↦
                    (Modules.pullback (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf))).obj (CanonicalTwists.obj F' hF' k))
                  (Int.natCast_add i j).symm) ≫
              component (i + j) =
        tensorHom (component i) (component j) ≫
          pullbackTensorLax (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι
              (tensorPowerUnit ((Modules.pullback g').obj L) i) (tensorPowerUnit ((Modules.pullback g').obj L) j) ≫
            (Modules.pullback (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)).ι).map (tensorPowerUnitAddIso ((Modules.pullback g').obj L) i j).hom) := sorry

/-- Pull back a graded twist comparison to the canonical domain of a commutative square. -/
def TwistComparison.pullbackAlongSquare
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] :
    TwistComparison hF' (domain f' deg' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)) (canonicalMap f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)) ((Modules.pullback g').obj L) where
  hom n :=
    (Modules.pullbackCongr (canonicalMap_eq_baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).hom.app (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
      (Modules.pullbackCompIso
            (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
            (baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).inv.app
        (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
        (Modules.pullback
              (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom).map
          (TwistComparison.baseChange f deg L ψ hF g hAlg hF' theta g' f' hf n) ≫
          (Modules.pullbackCompIso
                (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
                (domainInverseImage f deg L ψ g').ι).hom.app
            (tensorPowerUnit ((Modules.pullback g').obj L) n) ≫
            (Modules.pullbackCongr (domainBaseChangeIso_ι f deg L ψ g hAlg hF' g' f' hf)).hom.app (tensorPowerUnit ((Modules.pullback g').obj L) n)
  map_one := (TwistComparison.pullbackAlongSquare_laws f deg L ψ hF g hAlg hF' theta g' f' hf).1
  map_mul := (TwistComparison.pullbackAlongSquare_laws f deg L ψ hF g hAlg hF' theta g' f' hf).2

/-- `TwistComparison.pullbackAlongSquare` is the transport of `TwistComparison.baseChange` along
`domainBaseChangeIso`. -/
theorem TwistComparison.pullbackAlongSquare_hom
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)] (n : ℕ) :
    (TwistComparison.pullbackAlongSquare f deg L ψ hF g hAlg hF' theta g' f' hf).hom n =
      (Modules.pullbackCongr (canonicalMap_eq_baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).hom.app (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
        (Modules.pullbackCompIso
              (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
              (baseChangeMap f deg L ψ hF g hAlg hF' g' f' hf)).inv.app
          (CanonicalTwists.obj F' hF' (Int.ofNat n)) ≫
          (Modules.pullback
                (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom).map
            (TwistComparison.baseChange f deg L ψ hF g hAlg hF' theta g' f' hf n) ≫
            (Modules.pullbackCompIso
                  (domainBaseChangeIso f deg L ψ g hAlg hF' g' f' hf).hom
                  (domainInverseImage f deg L ψ g').ι).hom.app
              (tensorPowerUnit ((Modules.pullback g').obj L) n) ≫
              (Modules.pullbackCongr (domainBaseChangeIso_ι f deg L ψ g hAlg hF' g' f' hf)).hom.app (tensorPowerUnit ((Modules.pullback g').obj L) n) := by
  simp only [TwistComparison.pullbackAlongSquare]

/-- Pullback along a commutative square preserves the homogeneous section-square
characterization of a twist comparison. -/
theorem twistComparison_pullback_compatible
    {Y' : AlgebraicSpace S}
    {𝒜' : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift Y')}
    {deg' : DegreePieces 𝒜'} {F' : ProjFunctor Y' 𝒜'}
    (g : Y' ⟶ Y) (hAlg : AlgebraPullback g deg deg')
    (hF' : F'.IsAssociatedToQuadruples deg')
    (theta : TwistComparison hF (domain f deg L ψ) (canonicalMap f deg hF L ψ) L)
    {X' : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hf : g' ≫ f = f' ≫ g)
    [isInvertibleObject ((Modules.pullback g').obj L)]
    (htheta : ThetaCompatible f deg hF L ψ theta) :
    ThetaCompatible f' deg' hF' ((Modules.pullback g').obj L)
      (pullbackHomAlongSquare f deg L ψ g hAlg g' f' hf)
      (TwistComparison.pullbackAlongSquare f deg L ψ hF g hAlg hF' theta g' f' hf) := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
