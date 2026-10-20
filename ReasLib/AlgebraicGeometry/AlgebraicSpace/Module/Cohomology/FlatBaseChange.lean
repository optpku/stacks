module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.SchemeComparison.AffineBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.OverAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.HigherDirectImage

/-! # Flat base change for cohomology of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open Opposite TopCat TopologicalSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for definitional equality of higher direct images.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Affine comparison `Γ(Spec A, G) ⊗_A B ⟶ Γ(Spec B, s^* G)` for a module on `Spec A`. -/
private def moduleSpec_pullbackExtendScalars {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (G : (Spec (CommRingCat.of A)).Modules) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) ⟶
    (moduleSpecΓFunctor (R := CommRingCat.of B)).obj
      ((Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj G) :=
  ((tilde.adjunction (R := CommRingCat.of B)).homEquiv _ _)
    ((tilde.ChangeOfRings.Pullback.iso
        (CommRingCat.ofHom (algebraMap A B))).inv.app
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) ≫
      (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        ((tilde.adjunction (R := CommRingCat.of A)).counit.app G))

/-- The canonical map `H^i(X, ℱ) ⊗_A B ⟶ H^i(X', (g')^* ℱ)` of `B`-modules. -/
@[no_expose] def cohomologyBaseChangeHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) (i : ℕ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj (cohomologyOver σA f ℱ i) ⟶
      cohomologyOver σB f' ((pullback g').obj ℱ) i :=
  moduleSpec_pullbackExtendScalars ((toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i)) ≫
    (moduleSpecΓFunctor (R := CommRingCat.of B)).map
      (toScheme_pullbackHom σA σB hσ (higherDirectImage f ℱ i) ≫
        (toScheme (Over.mk σB)).map (higherDirectImageBaseChangeHom h_cart ℱ i))

/-- `cohomologyBaseChangeHom` is affine global-sections comparison followed by global sections
of `higherDirectImageBaseChangeHom`. -/
theorem cohomologyBaseChangeHom_eq {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g']
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) (i : ℕ) :
    cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i =
      (let G := (toScheme (Over.mk σA)).obj (higherDirectImage f ℱ i)
       ((tilde.adjunction (R := CommRingCat.of B)).homEquiv _ _)
    ((tilde.ChangeOfRings.Pullback.iso
        (CommRingCat.ofHom (algebraMap A B))).inv.app
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj G) ≫
      (Scheme.Modules.pullback
          (Spec.map (CommRingCat.ofHom (algebraMap A B)))).map
        ((tilde.adjunction (R := CommRingCat.of A)).counit.app G))) ≫
        (moduleSpecΓFunctor (R := CommRingCat.of B)).map
          (toScheme_pullbackHom σA σB hσ (higherDirectImage f ℱ i) ≫
            (toScheme (Over.mk σB)).map (higherDirectImageBaseChangeHom h_cart ℱ i)) :=
  by
    unfold cohomologyBaseChangeHom moduleSpec_pullbackExtendScalars
    rfl

/-- The affine cohomology comparison is an isomorphism under flat base change. -/
instance isIso_cohomologyBaseChangeHom {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] {X X' : AlgebraicSpace S}
    (σA : Spec (CommRingCat.of A) ⟶ S) (σB : Spec (CommRingCat.of B) ⟶ S)
    (hσ : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ σA = σB)
    (g' : X' ⟶ X) (f' : X' ⟶ ofOver (Over.mk σB)) (f : X ⟶ ofOver (Over.mk σA))
    (h_cart : IsPullback g' f' f
      (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ))
    [Flat (ofOverHomMk (Spec.map (CommRingCat.ofHom (algebraMap A B))) hσ)]
    [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules]
    [Abelian (ofOver (Over.mk σA)).Modules] [Abelian (ofOver (Over.mk σB)).Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIso (cohomologyBaseChangeHom σA σB hσ g' f' f h_cart ℱ i) :=
  sorry

variable {X' X Y' Y : AlgebraicSpace S}
variable {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The module higher-direct-image comparison morphism is an isomorphism when `g` is flat,
`f` is quasi-compact and quasi-separated, and `ℱ` is quasi-coherent. -/
instance isIso_higherDirectImageBaseChangeHom (h_cart : IsPullback g' f' f g)
    [Flat g] [Flat g'] [QuasiCompact f] [QuasiSeparated f]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ) :
    IsIso (higherDirectImageBaseChangeHom h_cart ℱ i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
