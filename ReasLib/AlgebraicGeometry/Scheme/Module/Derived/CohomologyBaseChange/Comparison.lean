/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Composition
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Pushout.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Composition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.AffinePullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.LeftDerived.Homotopy.Composition
open CategoryTheory.ModuleCat.Pushout.DerivedExtension
open AlgebraicGeometry.Scheme.Modules.Hom
open AlgebraicGeometry.RingedSpace.ModuleDerived
open scoped AlgebraicGeometry
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The tensor-product coefficient ring attached to two maps of commutative rings with
common source. -/
noncomputable def baseChangeRing (R A R' : CommRingCat.{u})
    (toA : R ⟶ A) (toR' : R ⟶ R') : CommRingCat.{u} :=
  -- Local instance justification (noncanonical choice): these explicit ring maps determine
  -- the two scalar structures used only to form their tensor product.
  let _ : Algebra R A := toA.hom.toAlgebra
  -- Local instance justification (noncanonical choice): this is the second explicit scalar
  -- structure belonging to the same tensor-product construction.
  let _ : Algebra R R' := toR'.hom.toAlgebra
  CommRingCat.of (A ⊗[R] R')

/-- The underlying type of `baseChangeRing` is the expected tensor product. -/
theorem baseChangeRing_coe (R A R' : CommRingCat.{u})
    (toA : R ⟶ A) (toR' : R ⟶ R') :
    baseChangeRing R A R' toA toR' = CommRingCat.of (let _ := toA.hom.toAlgebra
      let _ := toR'.hom.toAlgebra
      A ⊗[R] R') := sorry

/-- The right tensor-factor map into the pointwise tensor-product coefficient ring. -/
noncomputable def baseChangeRingRightMap
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R') :
    R' ⟶ baseChangeRing R A R' toA toR' :=
  -- Local instance justification (noncanonical choice): the two displayed ring maps determine
  -- the tensor-product coefficient ring and its right-factor inclusion.
  let _ : Algebra R A := toA.hom.toAlgebra
  -- Local instance justification (noncanonical choice): the second displayed ring map fixes the
  -- right tensor-factor scalar structure.
  let _ : Algebra R R' := toR'.hom.toAlgebra
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] A ⊗[R] R').toRingHom

/-- The left tensor-factor map into the pointwise tensor-product coefficient ring. -/
noncomputable def baseChangeRingLeftMap
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R') :
    A ⟶ baseChangeRing R A R' toA toR' :=
  -- Local instance justification (noncanonical choice): the two displayed ring maps determine
  -- the tensor-product coefficient ring and its left-factor inclusion.
  let _ : Algebra R A := toA.hom.toAlgebra
  -- Local instance justification (noncanonical choice): the second displayed ring map fixes the
  -- right tensor-factor scalar structure.
  let _ : Algebra R R' := toR'.hom.toAlgebra
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R').toRingHom

/-- The two left-hand scalar structures on the tensor-product coefficient ring form the
canonical tower. -/
theorem baseChangeRing_leftScalarTower
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R') :
    let _ : Algebra R A := toA.hom.toAlgebra
    let _ : Algebra R R' := toR'.hom.toAlgebra
    let _ : Algebra A (baseChangeRing R A R' toA toR') :=
      (baseChangeRingLeftMap R A R' toA toR').hom.toAlgebra
    let _ : Algebra R (baseChangeRing R A R' toA toR') :=
      (toA ≫ baseChangeRingLeftMap R A R' toA toR').hom.toAlgebra
    IsScalarTower R A (baseChangeRing R A R' toA toR') := sorry

/-- The two right-hand scalar structures on the tensor-product coefficient ring form the
canonical tower. -/
theorem baseChangeRing_rightScalarTower
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R') :
    let _ : Algebra R A := toA.hom.toAlgebra
    let _ : Algebra R R' := toR'.hom.toAlgebra
    let _ : Algebra R' (baseChangeRing R A R' toA toR') :=
      (baseChangeRingRightMap R A R' toA toR').hom.toAlgebra
    let _ : Algebra R (baseChangeRing R A R' toA toR') :=
      (toA ≫ baseChangeRingLeftMap R A R' toA toR').hom.toAlgebra
    IsScalarTower R R' (baseChangeRing R A R' toA toR') := sorry

/-- The tensor-product coefficient ring is the pushout of its two factor maps. -/
theorem baseChangeRing_isPushout
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R') :
    let _ : Algebra R A := toA.hom.toAlgebra
    let _ : Algebra R R' := toR'.hom.toAlgebra
    let _ : Algebra A (baseChangeRing R A R' toA toR') :=
      (baseChangeRingLeftMap R A R' toA toR').hom.toAlgebra
    let _ : Algebra R' (baseChangeRing R A R' toA toR') :=
      (baseChangeRingRightMap R A R' toA toR').hom.toAlgebra
    let _ : Algebra R (baseChangeRing R A R' toA toR') :=
      (toA ≫ baseChangeRingLeftMap R A R' toA toR').hom.toAlgebra
    let _ : IsScalarTower R A (baseChangeRing R A R' toA toR') :=
      baseChangeRing_leftScalarTower R A R' toA toR'
    let _ : IsScalarTower R R' (baseChangeRing R A R' toA toR') :=
      baseChangeRing_rightScalarTower R A R' toA toR'
    Algebra.IsPushout R R' A (baseChangeRing R A R' toA toR') := sorry

/-- The canonical underlying `R'`-linear derived base change `K ⊗ᴸ_R R'` of an
`A`-complex, obtained by restriction to `R` followed by derived extension to `R'`. -/
noncomputable def derivedBaseChangeUnderlying
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R') :
    CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} A))
      (DerivedCategory (ModuleCat.{u} R')) :=
  -- Local instance justification (noncanonical choice): the displayed structural map fixes the
  -- restriction-of-scalars route from `A` to `R`.
  let _ : Algebra R A := toA.hom.toAlgebra
  -- Local instance justification (noncanonical choice): the displayed base-change map fixes the
  -- derived extension route from `R` to `R'`.
  let _ : Algebra R R' := toR'.hom.toAlgebra
  baseDerived (R := R) (A := A) (R' := R')

/-- A strict `A ⊗[R] R'`-linear realization of derived base change.  Its restriction to
`R'` is canonically identified with restriction from `A` to `R` followed by derived extension
to `R'`; this rules out the generally different derived extension along `A ⟶ A ⊗[R] R'`. -/
structure DerivedBaseChangeModel.{v}
    (R A R' : CommRingCat.{v}) (toA : R ⟶ A) (toR' : R ⟶ R') where
  functor : CategoryTheory.Functor (DerivedCategory (ModuleCat.{v} A))
    (DerivedCategory (ModuleCat.{v} (baseChangeRing R A R' toA toR')))
  restrictionIso :
    functor ⋙ ModuleCat.derivedRestrictionOfScalars
        (baseChangeRingRightMap R A R' toA toR').hom ≅
      derivedBaseChangeUnderlying R A R' toA toR'

namespace DerivedBaseChangeModel

/-- Construct a strict tensor-ring lift from a functor and its canonical underlying
`R'`-linear comparison. -/
noncomputable def of
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (F : CategoryTheory.Functor (DerivedCategory (ModuleCat.{u} A))
      (DerivedCategory (ModuleCat.{u} (baseChangeRing R A R' toA toR'))))
    (restrictionIso :
      F ⋙ ModuleCat.derivedRestrictionOfScalars
          (baseChangeRingRightMap R A R' toA toR').hom ≅
        derivedBaseChangeUnderlying R A R' toA toR') :
    DerivedBaseChangeModel R A R' toA toR' where
  functor := F
  restrictionIso := restrictionIso

/-- The strict tensor-ring object representing `K ⊗ᴸ_R R'`. -/
noncomputable def obj
    {R A R' : CommRingCat.{u}} {toA : R ⟶ A} {toR' : R ⟶ R'}
    (L : DerivedBaseChangeModel R A R' toA toR')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    DerivedCategory (ModuleCat.{u} (baseChangeRing R A R' toA toR')) :=
  L.functor.obj K

/-- After restriction to `R'`, the strict tensor-ring lift is the canonical object
`K ⊗ᴸ_R R'`. -/
noncomputable def objRestrictionIso
    {R A R' : CommRingCat.{u}} {toA : R ⟶ A} {toR' : R ⟶ R'}
    (L : DerivedBaseChangeModel R A R' toA toR')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.derivedRestrictionOfScalars
      (baseChangeRingRightMap R A R' toA toR').hom).obj (L.obj K) ≅
        (derivedBaseChangeUnderlying R A R' toA toR').obj K :=
  L.restrictionIso.app K

end DerivedBaseChangeModel

/-- The first object in the affine comparison, namely derived sections over `A` restricted
to `R` and then derived-base-changed to `R'`. -/
noncomputable def affineBaseChangedSections
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (K : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} R') :=
  (ModuleCat.derivedExtensionOfScalars toR'.hom).obj
    ((ModuleCat.derivedRestrictionOfScalars toA.hom).obj K)

/-- `affineBaseChangedSections` is restriction to the base followed by derived extension
to the changed base. -/
theorem affineBaseChangedSections_def
    (R A R' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    affineBaseChangedSections R A R' toA toR' K =
      (ModuleCat.derivedExtensionOfScalars toR'.hom).obj
        ((ModuleCat.derivedRestrictionOfScalars toA.hom).obj K) := sorry

/-- The middle object in the affine comparison, namely derived extension from `A` to
`A'`, viewed over the changed base ring `R'`. -/
noncomputable def affinePullbackSections
    (A R' A' : CommRingCat.{u}) (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (K : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} R') :=
  (ModuleCat.derivedRestrictionOfScalars toTarget.hom).obj
    ((ModuleCat.derivedExtensionOfScalars toA'.hom).obj K)

/-- `affinePullbackSections` is derived extension to `A'` followed by restriction to
`R'`. -/
theorem affinePullbackSections_def
    (A R' A' : CommRingCat.{u}) (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    affinePullbackSections A R' A' toA' toTarget K =
      (ModuleCat.derivedRestrictionOfScalars toTarget.hom).obj
        ((ModuleCat.derivedExtensionOfScalars toA'.hom).obj K) := sorry

/-- Derived target sections over `A'`, viewed over the changed base ring `R'`. -/
noncomputable def affineTargetSections
    (R' A' : CommRingCat.{u}) (toTarget : R' ⟶ A')
    (K' : DerivedCategory (ModuleCat.{u} A')) : DerivedCategory (ModuleCat.{u} R') :=
  (ModuleCat.derivedRestrictionOfScalars toTarget.hom).obj K'

/-- `affineTargetSections` is restriction of scalars from `A'` to `R'`. -/
theorem affineTargetSections_def
    (R' A' : CommRingCat.{u}) (toTarget : R' ⟶ A')
    (K' : DerivedCategory (ModuleCat.{u} A')) :
    affineTargetSections R' A' toTarget K' =
      (ModuleCat.derivedRestrictionOfScalars toTarget.hom).obj K' := sorry

/-- The two displayed derived morphisms on a compatible affine chart. The fixed source and
target complexes are the actual derived section objects, and the comparison is formed in
`D(R')` from the four section-ring maps. -/
structure AffineBaseChangeComparison.{v}
    (R A R' A' : CommRingCat.{v}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (K : DerivedCategory (ModuleCat.{v} A))
    (K' : DerivedCategory (ModuleCat.{v} A')) where
  toPullbackSections :
    affineBaseChangedSections R A R' toA toR' K ⟶
      affinePullbackSections A R' A' toA' toTarget K
  toTargetSections :
    affinePullbackSections A R' A' toA' toTarget K ⟶
      affineTargetSections R' A' toTarget K'

namespace AffineBaseChangeComparison

/-- Construct an affine comparison from the two displayed arrows. -/
noncomputable def of
    (R A R' A' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (first : affineBaseChangedSections R A R' toA toR' K ⟶
      affinePullbackSections A R' A' toA' toTarget K)
    (second : affinePullbackSections A R' A' toA' toTarget K ⟶
      affineTargetSections R' A' toTarget K') :
    AffineBaseChangeComparison R A R' A' toA toR' toA' toTarget K K' where
  toPullbackSections := first
  toTargetSections := second

/-- The displayed affine base-change composite. -/
noncomputable def map
    {R A R' A' : CommRingCat.{u}} {toA : R ⟶ A} {toR' : R ⟶ R'}
    {toA' : A ⟶ A'} {toTarget : R' ⟶ A'}
    {K : DerivedCategory (ModuleCat.{u} A)}
    {K' : DerivedCategory (ModuleCat.{u} A')}
    (D : AffineBaseChangeComparison R A R' A' toA toR' toA' toTarget K K') :
    affineBaseChangedSections R A R' toA toR' K ⟶
      affineTargetSections R' A' toTarget K' :=
  D.toPullbackSections ≫ D.toTargetSections

/-- The affine comparison map is the composite of its two displayed arrows. -/
theorem map_eq
    {R A R' A' : CommRingCat.{u}} {toA : R ⟶ A} {toR' : R ⟶ R'}
    {toA' : A ⟶ A'} {toTarget : R' ⟶ A'}
    {K : DerivedCategory (ModuleCat.{u} A)}
    {K' : DerivedCategory (ModuleCat.{u} A')}
    (D : AffineBaseChangeComparison R A R' A' toA toR' toA' toTarget K K') :
    D.map = D.toPullbackSections ≫ D.toTargetSections := sorry

end AffineBaseChangeComparison

/-- Derived extension of affine sections from the source affine ring to the target affine
section ring. This retains the `A'`-module structure needed to localize at points of the
target affine open. -/
noncomputable def affineTargetLinearSource
    (A A' : CommRingCat.{u}) (toA' : A ⟶ A')
    (K : DerivedCategory (ModuleCat.{u} A)) : DerivedCategory (ModuleCat.{u} A') :=
  (ModuleCat.derivedExtensionOfScalars toA'.hom).obj K

/-- `affineTargetLinearSource` is derived extension along the target affine-ring map. -/
theorem affineTargetLinearSource_def
    (A A' : CommRingCat.{u}) (toA' : A ⟶ A')
    (K : DerivedCategory (ModuleCat.{u} A)) :
    affineTargetLinearSource A A' toA' K =
      (ModuleCat.derivedExtensionOfScalars toA'.hom).obj K := sorry

/-- An `A'`-linear lift of the displayed affine base-change composite. The comparison
isomorphism and `restriction_eq` identify its restriction to `R'` with the two-arrow
affine composite. -/
structure AffineTargetLinearComparison.{v}
    (R A R' A' : CommRingCat.{v}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (K : DerivedCategory (ModuleCat.{v} A))
    (K' : DerivedCategory (ModuleCat.{v} A'))
    (displayed : AffineBaseChangeComparison R A R' A' toA toR' toA' toTarget K K') where
  map : affineTargetLinearSource A A' toA' K ⟶ K'
  sourceRestrictionIso :
    affineBaseChangedSections R A R' toA toR' K ≅
      (ModuleCat.derivedRestrictionOfScalars toTarget.hom).obj
        (affineTargetLinearSource A A' toA' K)
  restriction_eq :
    sourceRestrictionIso.hom ≫
        (ModuleCat.derivedRestrictionOfScalars toTarget.hom).map map = displayed.map

namespace AffineTargetLinearComparison

/-- Construct a target-section-ring-linear comparison from its map and its restriction
identification with the displayed affine composite. -/
noncomputable def of
    (R A R' A' : CommRingCat.{u}) (toA : R ⟶ A) (toR' : R ⟶ R')
    (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (displayed : AffineBaseChangeComparison R A R' A' toA toR' toA' toTarget K K')
    (map : affineTargetLinearSource A A' toA' K ⟶ K')
    (sourceRestrictionIso :
      affineBaseChangedSections R A R' toA toR' K ≅
        (ModuleCat.derivedRestrictionOfScalars toTarget.hom).obj
          (affineTargetLinearSource A A' toA' K))
    (restriction_eq : sourceRestrictionIso.hom ≫
      (ModuleCat.derivedRestrictionOfScalars toTarget.hom).map map = displayed.map) :
    AffineTargetLinearComparison R A R' A' toA toR' toA' toTarget K K' displayed where
  map := map
  sourceRestrictionIso := sourceRestrictionIso
  restriction_eq := restriction_eq

/-- Restricting a target-linear comparison to `R'` recovers the displayed affine composite. -/
theorem map_restrict
    {R A R' A' : CommRingCat.{u}} {toA : R ⟶ A} {toR' : R ⟶ R'}
    {toA' : A ⟶ A'} {toTarget : R' ⟶ A'}
    {K : DerivedCategory (ModuleCat.{u} A)}
    {K' : DerivedCategory (ModuleCat.{u} A')}
    {displayed : AffineBaseChangeComparison R A R' A' toA toR' toA' toTarget K K'}
    (D : AffineTargetLinearComparison R A R' A' toA toR' toA' toTarget K K' displayed) :
    D.sourceRestrictionIso.hom ≫
        (ModuleCat.derivedRestrictionOfScalars toTarget.hom).map D.map = displayed.map := sorry

end AffineTargetLinearComparison

/-- The map `𝒪_{S,f(g'(x'))} ⟶ 𝒪_{S',f'(x')}` induced by `g`, with its source transported
along the pointwise equality supplied by the cartesian square. -/
noncomputable def baseChangeStalkMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    S.presheaf.stalk (f (g' x')) ⟶ S'.presheaf.stalk (f' x') :=
  (S.presheaf.stalkCongr (.of_eq
    (congrArg (fun k : X' ⟶ S ↦ k x') sq.w))).hom ≫ g.stalkMap (f' x')

/-- `baseChangeStalkMap` is the stalk map of `g` transported along the equality of the two
composites in the cartesian square. -/
theorem baseChangeStalkMap_def
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    baseChangeStalkMap g' f' f g sq x' =
      (S.presheaf.stalkCongr (.of_eq
        (congrArg (fun k : X' ⟶ S ↦ k x') sq.w))).hom ≫
          g.stalkMap (f' x') := sorry

/-- The four canonical stalk-ring maps induced by the cartesian square commute. -/
theorem baseChangeStalkMap_comm
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    f.stalkMap (g' x') ≫ g'.stalkMap x' =
      baseChangeStalkMap g' f' f g sq x' ≫ f'.stalkMap x' := sorry

/-- The compatibility equation needed to view the right-hand map of a commuting ring square
as a morphism of algebras over its upper-left corner. -/
theorem baseChangeRingMap_right_commutes
    (R A R' A' : CommRingCat.{u})
    (toA : R ⟶ A) (toR' : R ⟶ R') (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (comm : toA ≫ toA' = toR' ≫ toTarget) (r : R) :
    toTarget.hom (toR'.hom r) = toA'.hom (toA.hom r) := sorry

/-- The upper-right map of a commuting ring square respects the scalar structure induced by
the upper route. -/
theorem baseChangeRingMap_left_commutes
    (R A A' : CommRingCat.{u}) (toA : R ⟶ A) (toA' : A ⟶ A') (r : R) :
    toA'.hom (toA.hom r) = (toA ≫ toA').hom r := sorry

/-- The two factor maps of a commuting square have commuting images in its target
commutative ring. -/
theorem baseChangeRingMap_commute
    (A R' A' : CommRingCat.{u}) (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (a : A) (r' : R') :
    Commute (toA'.hom a) (toTarget.hom r') := sorry

/-- The canonical map from a tensor-product base-change ring induced by a commuting square of
commutative rings. -/
noncomputable def baseChangeRingMap
    (R A R' A' : CommRingCat.{u})
    (toA : R ⟶ A) (toR' : R ⟶ R') (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (comm : toA ≫ toA' = toR' ≫ toTarget) :
    baseChangeRing R A R' toA toR' ⟶ A' :=
  -- Local instance justification (noncanonical choice): the explicit upper ring map fixes the
  -- scalar structure used to form this tensor product.
  let _ : Algebra R A := toA.hom.toAlgebra
  -- Local instance justification (noncanonical choice): the explicit lower ring map fixes the
  -- second scalar structure used to form this tensor product.
  let _ : Algebra R R' := toR'.hom.toAlgebra
  -- Local instance justification (noncanonical choice): the composite along the upper and
  -- right edges fixes the target scalar structure.
  let _ : Algebra R A' := (toA ≫ toA').hom.toAlgebra
  let left : A →ₐ[R] A' :=
    { toRingHom := toA'.hom
      commutes' := baseChangeRingMap_left_commutes R A A' toA toA' }
  let right : R' →ₐ[R] A' :=
    { toRingHom := toTarget.hom
      commutes' := baseChangeRingMap_right_commutes R A R' A'
        toA toR' toA' toTarget comm }
  CommRingCat.ofHom
    (Algebra.TensorProduct.lift left right
      (baseChangeRingMap_commute A R' A' toA' toTarget)).toRingHom

/-- The tensor-product map induced by a commuting square restricts to its upper-right map on
the left tensor factor. -/
theorem baseChangeRingMap_includeLeft
    (R A R' A' : CommRingCat.{u})
    (toA : R ⟶ A) (toR' : R ⟶ R') (toA' : A ⟶ A') (toTarget : R' ⟶ A')
    (comm : toA ≫ toA' = toR' ≫ toTarget) :
    (baseChangeRingMap R A R' A' toA toR' toA' toTarget comm).hom.comp
        (-- Local instance justification (noncanonical choice): `toA` fixes the left tensor
         -- factor in this readout of `baseChangeRingMap`.
         let _ : Algebra R A := toA.hom.toAlgebra
         -- Local instance justification (noncanonical choice): `toR'` fixes the right tensor
         -- factor in this readout of `baseChangeRingMap`.
         let _ : Algebra R R' := toR'.hom.toAlgebra
         Algebra.TensorProduct.includeLeftRingHom) = toA'.hom := sorry

/-- The tensor-product stalk-ring map induced by a cartesian square at `x'`. -/
noncomputable def pointTensorMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    baseChangeRing (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (S'.presheaf.stalk (f' x')) (f.stalkMap (g' x'))
        (baseChangeStalkMap g' f' f g sq x') ⟶
      X'.presheaf.stalk x' :=
  baseChangeRingMap (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
    (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x')
    (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')
    (g'.stalkMap x') (f'.stalkMap x') (baseChangeStalkMap_comm g' f' f g sq x')

/-- The pointwise tensor-product map restricts to the stalk map of `g'` on the source-stalk
factor. -/
theorem pointTensorMap_includeLeft
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    (pointTensorMap g' f' f g sq x').hom.comp
        (-- Local instance justification (noncanonical choice): the stalk map of `f` fixes the
         -- left tensor-factor scalar structure at `x'`.
         let _ : Algebra (S.presheaf.stalk (f (g' x')))
            (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
         -- Local instance justification (noncanonical choice): the transported stalk map of
         -- `g` fixes the right tensor-factor scalar structure at `x'`.
         let _ : Algebra (S.presheaf.stalk (f (g' x')))
            (S'.presheaf.stalk (f' x')) :=
           (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
         Algebra.TensorProduct.includeLeftRingHom) = (g'.stalkMap x').hom := sorry

/-- The map from the scalar-extended stalk of `K` to the stalk of `K'`, obtained from the
derived pullback-stalk comparison and `α`. -/
noncomputable def pointPullbackStalkMap
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') :
    (ModuleCat.derivedExtensionOfScalars (g'.stalkMap x').hom).obj
        (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')) ⟶
      Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x' :=
  (AlgebraicGeometry.RingedSpace.modulePullbackDerived.Stalk.iso
    g'.toLRSHom.toShHom x').hom.app
      ((ModuleDerived.Quasicoherent.inclusion X).obj K) ≫
    (Stalk.functor x').map ((pullback.inclusionIso g').inv.app K) ≫
    (Stalk.functor x').map ((ModuleDerived.Quasicoherent.inclusion X').map α)

/-- `pointPullbackStalkMap` is the pullback-stalk comparison followed by the stalk of `α`. -/
theorem pointPullbackStalkMap_eq
    {X' X : Scheme.{u}} (g' : X' ⟶ X) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') :
    pointPullbackStalkMap g' K K' α x' =
      (AlgebraicGeometry.RingedSpace.modulePullbackDerived.Stalk.iso
        g'.toLRSHom.toShHom x').hom.app
          ((ModuleDerived.Quasicoherent.inclusion X).obj K) ≫
        (Stalk.functor x').map ((pullback.inclusionIso g').inv.app K) ≫
        (Stalk.functor x').map ((ModuleDerived.Quasicoherent.inclusion X').map α) := sorry

/-- The canonical derived point comparison.  It first extends
the stalk complex to the tensor-product coefficient ring, then extends along the canonical
map to `𝒪_{X',x'}`, and finally applies the stalk map induced by `α`. -/
noncomputable def canonicalPointComparisonMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') :
    (ModuleCat.derivedExtensionOfScalars (pointTensorMap g' f' f g sq x').hom).obj
        ((ModuleCat.derivedExtensionOfScalars
          (baseChangeRingLeftMap (S.presheaf.stalk (f (g' x')))
            (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
            (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')).hom).obj
              (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x'))) ⟶
      Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x' :=
  (ModuleCat.derivedExtensionOfScalarsCompIso
      (baseChangeRingLeftMap (S.presheaf.stalk (f (g' x')))
        (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
        (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')).hom
      (pointTensorMap g' f' f g sq x').hom (g'.stalkMap x').hom
      (pointTensorMap_includeLeft g' f' f g sq x')).hom.app
        (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')) ≫
    pointPullbackStalkMap g' K K' α x'

/-- The canonical degree-`i` cohomology base-change map at `x'`. -/
noncomputable def canonicalPointCohomologyMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :=
  -- Local instance justification (noncanonical choice): the stalk map of `f` fixes the
  -- source-ring action used in the tensor-product coefficient ring.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the transported stalk map of `g`
  -- fixes the changed-base action in the tensor-product coefficient ring.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (S'.presheaf.stalk (f' x')) :=
    (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
  ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g sq x').hom
    ((ModuleCat.derivedExtensionOfScalars
      (baseChangeRingLeftMap (S.presheaf.stalk (f (g' x')))
        (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
        (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')).hom).obj
          (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')))
    (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x')
    (canonicalPointComparisonMap g' f' f g sq K K' α x') i


/-- The square of section-ring maps on a compatible affine chart commutes. -/
theorem affineChart_sectionRingSquare
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    f.appLE V U hU ≫ g'.appLE U U' inf_le_left =
      g.appLE V V' hV' ≫ f'.appLE V' U' inf_le_right := sorry

/-- The scalar structures on the left side of a compatible affine section-ring square form a
scalar tower. -/
theorem affineChart_leftScalarTower
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    let R := RingedSpace.sectionsRingOnOpen S.toRingedSpace V
    let A := RingedSpace.sectionsRingOnOpen X.toRingedSpace U
    let A' := RingedSpace.sectionsRingOnOpen X'.toRingedSpace U'
    -- Local instance justification (noncanonical choice): the chosen chart map fixes the
    -- `R`-algebra structure on `A`.
    let _ : Algebra R A := (f.appLE V U hU).hom.toAlgebra
    -- Local instance justification (noncanonical choice): the pullback chart map fixes the
    -- `A`-algebra structure on `A'`.
    let _ : Algebra A A' := (g'.appLE U U' inf_le_left).hom.toAlgebra
    -- Local instance justification (defeq pin): the upper composite is the scalar action whose
    -- tower law is asserted by this declaration.
    let _ : Algebra R A' := (f.appLE V U hU ≫ g'.appLE U U' inf_le_left).hom.toAlgebra
    IsScalarTower R A A' := sorry

/-- The scalar structures on the right side of a compatible affine section-ring square form a
scalar tower. -/
theorem affineChart_rightScalarTower
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    let R := RingedSpace.sectionsRingOnOpen S.toRingedSpace V
    let R' := RingedSpace.sectionsRingOnOpen S'.toRingedSpace V'
    let A' := RingedSpace.sectionsRingOnOpen X'.toRingedSpace U'
    -- Local instance justification (noncanonical choice): the chosen base chart map fixes the
    -- `R`-algebra structure on `R'`.
    let _ : Algebra R R' := (g.appLE V V' hV').hom.toAlgebra
    -- Local instance justification (noncanonical choice): the target chart map fixes the
    -- `R'`-algebra structure on `A'`.
    let _ : Algebra R' A' := (f'.appLE V' U' inf_le_right).hom.toAlgebra
    -- Local instance justification (defeq pin): the upper composite agrees propositionally
    -- with the lower composite and fixes the common `R`-action used by this tower statement.
    let _ : Algebra R A' := (f.appLE V U hU ≫ g'.appLE U U' inf_le_left).hom.toAlgebra
    IsScalarTower R R' A' := sorry

/-- The section-ring square of a cartesian affine chart is a pushout square of algebras. -/
theorem affineChart_sectionsIsPushout
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    let R := RingedSpace.sectionsRingOnOpen S.toRingedSpace V
    let A := RingedSpace.sectionsRingOnOpen X.toRingedSpace U
    let R' := RingedSpace.sectionsRingOnOpen S'.toRingedSpace V'
    let A' := RingedSpace.sectionsRingOnOpen X'.toRingedSpace U'
    -- Local instance justification (noncanonical choice): the chosen chart map fixes the
    -- `R`-algebra structure on `A`.
    let _ : Algebra R A := (f.appLE V U hU).hom.toAlgebra
    -- Local instance justification (noncanonical choice): the chosen base chart map fixes the
    -- `R`-algebra structure on `R'`.
    let _ : Algebra R R' := (g.appLE V V' hV').hom.toAlgebra
    -- Local instance justification (defeq pin): the upper composite fixes the common
    -- `R`-algebra structure on the target chart.
    let _ : Algebra R A' := (f.appLE V U hU ≫ g'.appLE U U' inf_le_left).hom.toAlgebra
    -- Local instance justification (noncanonical choice): the pullback chart map fixes the
    -- `A`-algebra structure on `A'`.
    let _ : Algebra A A' := (g'.appLE U U' inf_le_left).hom.toAlgebra
    -- Local instance justification (noncanonical choice): the target chart map fixes the
    -- `R'`-algebra structure on `A'`.
    let _ : Algebra R' A' := (f'.appLE V' U' inf_le_right).hom.toAlgebra
    -- Local instance justification (proof-local temporary data): this is the left scalar tower
    -- attached to the fixed commuting section-ring square.
    let _ : IsScalarTower R A A' :=
      affineChart_leftScalarTower g' f' f g sq V U V' hU hV'
    -- Local instance justification (proof-local temporary data): this is the right scalar tower
    -- attached to the fixed commuting section-ring square.
    let _ : IsScalarTower R R' A' :=
      affineChart_rightScalarTower g' f' f g sq V U V' hU hV'
    Algebra.IsPushout R R' A A' := sorry

/-- The canonical derived pushout base-change arrow on a compatible affine chart. -/
noncomputable def affineChartFirstMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    affineBaseChangedSections
        (RingedSpace.sectionsRingOnOpen S.toRingedSpace V)
        (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V')
        (f.appLE V U hU) (g.appLE V V' hV')
        ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj
          ((ModuleDerived.Quasicoherent.inclusion X).obj K)) ⟶
      affinePullbackSections
        (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V')
        (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
        (g'.appLE U U' inf_le_left) (f'.appLE V' U' inf_le_right)
        ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj
          ((ModuleDerived.Quasicoherent.inclusion X).obj K)) :=
  let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
  let R := RingedSpace.sectionsRingOnOpen S.toRingedSpace V
  let A := RingedSpace.sectionsRingOnOpen X.toRingedSpace U
  let R' := RingedSpace.sectionsRingOnOpen S'.toRingedSpace V'
  let A' := RingedSpace.sectionsRingOnOpen X'.toRingedSpace U'
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra R A := (f.appLE V U hU).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra R R' := (g.appLE V V' hV').hom.toAlgebra
  -- Local instance justification (noncanonical choice): the composite through `U` fixes the
  -- ambient `R`-algebra structure on the target chart.
  let _ : Algebra R A' := (f.appLE V U hU ≫ g'.appLE U U' inf_le_left).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra A A' := (g'.appLE U U' inf_le_left).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra R' A' := (f'.appLE V' U' inf_le_right).hom.toAlgebra
  -- Local instance justification (proof-local temporary data): this witnesses the left route
  -- through the fixed affine section-ring square.
  let _ : IsScalarTower R A A' :=
    affineChart_leftScalarTower g' f' f g sq V U V' hU hV'
  -- Local instance justification (proof-local temporary data): this witnesses the right route
  -- through the fixed affine section-ring square.
  let _ : IsScalarTower R R' A' :=
    affineChart_rightScalarTower g' f' f g sq V U V' hU hV'
  -- Local instance justification (proof-local temporary data): cartesianness of the affine
  -- chart supplies precisely the pushout instance consumed by the comparison.
  let _ : Algebra.IsPushout R R' A A' :=
    affineChart_sectionsIsPushout g' f' f g sq V U V' hU hV'
  comparisonApp
    ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj
      ((ModuleDerived.Quasicoherent.inclusion X).obj K))

/-- The canonical derived pushout base-change arrow applied to an explicit affine module model. -/
noncomputable def affineChartFirstMapOf
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V)
    (M : DerivedCategory (ModuleCat
      (RingedSpace.sectionsRingOnOpen X.toRingedSpace U))) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    affineBaseChangedSections
        (RingedSpace.sectionsRingOnOpen S.toRingedSpace V)
        (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V')
        (f.appLE V U hU) (g.appLE V V' hV') M ⟶
      affinePullbackSections
        (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V')
        (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
        (g'.appLE U U' inf_le_left) (f'.appLE V' U' inf_le_right) M :=
  let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
  let R := RingedSpace.sectionsRingOnOpen S.toRingedSpace V
  let A := RingedSpace.sectionsRingOnOpen X.toRingedSpace U
  let R' := RingedSpace.sectionsRingOnOpen S'.toRingedSpace V'
  let A' := RingedSpace.sectionsRingOnOpen X'.toRingedSpace U'
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra R A := (f.appLE V U hU).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra R R' := (g.appLE V V' hV').hom.toAlgebra
  -- Local instance justification (noncanonical choice): the composite through `U` fixes the
  -- ambient `R`-algebra structure on the target chart.
  let _ : Algebra R A' := (f.appLE V U hU ≫ g'.appLE U U' inf_le_left).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra A A' := (g'.appLE U U' inf_le_left).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the chart fixes this scalar map.
  let _ : Algebra R' A' := (f'.appLE V' U' inf_le_right).hom.toAlgebra
  -- Local instance justification (proof-local temporary data): this witnesses the left route
  -- through the fixed affine section-ring square.
  let _ : IsScalarTower R A A' :=
    affineChart_leftScalarTower g' f' f g sq V U V' hU hV'
  -- Local instance justification (proof-local temporary data): this witnesses the right route
  -- through the fixed affine section-ring square.
  let _ : IsScalarTower R R' A' :=
    affineChart_rightScalarTower g' f' f g sq V U V' hU hV'
  -- Local instance justification (proof-local temporary data): cartesianness of the affine
  -- chart supplies precisely the pushout instance consumed by the comparison.
  let _ : Algebra.IsPushout R R' A A' :=
    affineChart_sectionsIsPushout g' f' f g sq V U V' hU hV'
  comparisonApp M

/-- On a compatible affine chart, extend derived sections along the map induced by `g'` and
then restrict scalars along the map induced by `f'`. -/
noncomputable def affinePullbackSectionsFunctor
    {X' X S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S')
    (U : X.affineOpens) (V' : S'.affineOpens) :
    CategoryTheory.Functor (ModuleDerived.Quasicoherent X)
      (DerivedCategory (ModuleCat
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V'))) :=
  let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
  ModuleDerived.Quasicoherent.inclusion X ⋙
    RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U ⋙
    ModuleCat.derivedExtensionOfScalars (g'.appLE U U' inf_le_left).hom ⋙
    ModuleCat.derivedRestrictionOfScalars (f'.appLE V' U' inf_le_right).hom

/-- On a compatible affine chart, take derived sections of the pullback and then view them
over the changed base ring. -/
noncomputable def affineTargetPullbackSectionsFunctor
    {X' X S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S')
    (U : X.affineOpens) (V' : S'.affineOpens) :
    CategoryTheory.Functor (ModuleDerived.Quasicoherent X)
      (DerivedCategory (ModuleCat
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V'))) :=
  let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
  pullback g' ⋙ ModuleDerived.Quasicoherent.inclusion X' ⋙
    RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U' ⋙
    ModuleCat.derivedRestrictionOfScalars (f'.appLE V' U' inf_le_right).hom

/-- The right tensor-factor map for the stalk square at `x'`. -/
noncomputable def pointBaseChangeRightMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    S'.presheaf.stalk (f' x') ⟶
      baseChangeRing (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
        (S'.presheaf.stalk (f' x')) (f.stalkMap (g' x'))
        (baseChangeStalkMap g' f' f g sq x') :=
  -- Local instance justification (noncanonical choice): the stalk map of `f` fixes the left
  -- tensor-factor scalar structure at `x'`.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the transported stalk map of `g`
  -- fixes the right tensor-factor scalar structure at `x'`.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (S'.presheaf.stalk (f' x')) :=
    (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight :
      S'.presheaf.stalk (f' x') →ₐ[S.presheaf.stalk (f (g' x'))]
        X.presheaf.stalk (g' x') ⊗[S.presheaf.stalk (f (g' x'))]
          S'.presheaf.stalk (f' x')).toRingHom

/-- The canonical underlying stalkwise derived base change: restrict from
`𝒪_{X,g'(x')}` to `𝒪_{S,f(g'(x'))}` and then derive extension to
`𝒪_{S',f'(x')}`. -/
noncomputable def pointBaseChangeUnderlyingFunctor
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (x' : X') :
    CategoryTheory.Functor
      (DerivedCategory (ModuleCat (X.presheaf.stalk (g' x'))))
      (DerivedCategory (ModuleCat (S'.presheaf.stalk (f' x')))) :=
  ModuleCat.derivedRestrictionOfScalars (f.stalkMap (g' x')).hom ⋙
    ModuleCat.derivedExtensionOfScalars (baseChangeStalkMap g' f' f g sq x').hom

/-- A compatible affine quadruple for a cartesian square of schemes. -/
structure AffineBaseChangeChart.{v}
    {X' X S' S : Scheme.{v}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) where
  V : S.affineOpens
  U : X.affineOpens
  V' : S'.affineOpens
  U' : X'.affineOpens
  mapU : U ≤ f ⁻¹ᵁ V
  mapV' : V' ≤ g ⁻¹ᵁ V
  pullback_eq : (U' : X'.Opens) =
    g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)

namespace AffineBaseChangeChart

/-- Construct a compatible affine chart from its four affine opens and compatibility data. -/
noncomputable def of
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (U' : X'.affineOpens) (mapU : U ≤ f ⁻¹ᵁ V) (mapV' : V' ≤ g ⁻¹ᵁ V)
    (pullback_eq : (U' : X'.Opens) =
      g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)) :
    AffineBaseChangeChart g' f' f g where
  V := V
  U := U
  V' := V'
  U' := U'
  mapU := mapU
  mapV' := mapV'
  pullback_eq := pullback_eq

/-- A compatible affine chart satisfies the two mapping conditions and the pullback-open
identity from its construction. -/
theorem spec
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (c : AffineBaseChangeChart g' f' f g) :
    c.U ≤ f ⁻¹ᵁ c.V ∧ c.V' ≤ g ⁻¹ᵁ c.V ∧
      (c.U' : X'.Opens) =
        g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens) := sorry

/-- Every point of the pullback affine open maps into its chosen affine open in `S'`. -/
theorem mapU'
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (c : AffineBaseChangeChart g' f' f g) :
    (c.U' : X'.Opens) ≤ f' ⁻¹ᵁ (c.V' : S'.Opens) := sorry

/-- Membership in the chosen target affine open gives membership in its pullback-open
presentation. -/
theorem memPullback
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (c : AffineBaseChangeChart g' f' f g) {x' : X'}
    (hx' : x' ∈ (c.U' : X'.Opens)) :
    x' ∈ g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens) := sorry

end AffineBaseChangeChart

/-- The affine open presented by the fiber-product equation of a compatible chart. -/
def AffineBaseChangeChart.inducedU'
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (c : AffineBaseChangeChart g' f' f g) : X'.affineOpens :=
  ⟨g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens),
    c.pullback_eq ▸ c.U'.2⟩

/-- The affine open induced by the fiber-product presentation is the chart's chosen
target affine open. -/
theorem AffineBaseChangeChart.inducedU'_eq
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (c : AffineBaseChangeChart g' f' f g) : c.inducedU' = c.U' := sorry

/-- Iterated derived pullback on `ModuleDerived.Quasicoherent` is canonically isomorphic to pullback along
the composite. -/
noncomputable def pullbackCompObjIso
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (K : ModuleDerived.Quasicoherent X) :
    (pullback g).obj ((pullback f).obj K) ≅ (pullback (g ≫ f)).obj K :=
  (ModuleDerived.quasicoherentProperty Z).fullyFaithfulι.preimageIso
    ((pullback.inclusionIso g).app ((pullback f).obj K) ≪≫
      (RingedSpace.modulePullbackDerived g.toLRSHom.toShHom).mapIso
        ((pullback.inclusionIso f).app K) ≪≫
      (RingedSpace.modulePullbackDerived.compIso g.toLRSHom.toShHom
        f.toLRSHom.toShHom
        (RingedSpace.modulePullbackDerived.compComparison_isIso
          g.toLRSHom.toShHom f.toLRSHom.toShHom)).app ((ModuleDerived.Quasicoherent.inclusion X).obj K) ≪≫
      (pullback.inclusionIso (g ≫ f)).symm.app K)

/-- The affine functor is an equivalence, by the derived module equivalence followed by the
affine cohomology comparison. -/
noncomputable instance affineFunctorIsEquivalence (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    Functor.IsEquivalence (affineFunctor A) :=
  (((affineModuleEquivalence A).mapDerivedCategory.trans
    (DerivedCategory.CohomologyIn.Comparison.functor
      (RingedSpace.quasiCoherentModuleProperty
        (Spec A).toRingedSpace)).asEquivalence)).isEquivalence_functor

/-- The canonical affine module model of a derived quasi-coherent complex on an affine open. -/
noncomputable def affineLocalModel
    {X : Scheme.{u}} (K : ModuleDerived.Quasicoherent X) (U : X.affineOpens) :
    DerivedCategory (ModuleCat
      (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)) :=
  (affineFunctor (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)).inv.obj
    ((pullback U.2.fromSpec).obj K)

/-- The affine module model is a canonical representative of derived sections on the affine
open. -/
theorem affineLocalModel_represents_sections
    {X : Scheme.{u}} (K : ModuleDerived.Quasicoherent X) (U : X.affineOpens) :
    IsIsomorphic (affineLocalModel K U)
      ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj
        ((ModuleDerived.Quasicoherent.inclusion X).obj K)) := sorry

/-- The canonical `𝒪_{X'}(U')`-linear second arrow of the affine base-change comparison. -/
noncomputable def canonicalAffineLinearMap
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :
    let U' := c.inducedU'
    (ModuleCat.derivedExtensionOfScalars (g'.appLE c.U U' inf_le_left).hom).obj
        (affineLocalModel K c.U) ⟶ affineLocalModel K' U' :=
  let U' := c.inducedU'
  let A := RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U
  let A' := RingedSpace.sectionsRingOnOpen X'.toRingedSpace U'
  let φ := g'.appLE c.U U' inf_le_left
  let E := (pullback c.U.2.fromSpec).obj K
  let E' := (pullback U'.2.fromSpec).obj K'
  let hcomm : Spec.map φ ≫ c.U.2.fromSpec = U'.2.fromSpec ≫ g' :=
    IsAffineOpen.SpecMap_appLE_fromSpec g' c.U.2 U'.2 inf_le_left
  (affineFunctor A').preimage
    ((affinePullbackIso φ).hom.app (affineLocalModel K c.U) ≫
      (pullback (Spec.map φ)).map
        ((affineFunctor A).asEquivalence.counitIso.hom.app E) ≫
      (pullbackCompObjIso c.U.2.fromSpec (Spec.map φ) K).hom ≫
      eqToHom (congrArg (fun q : Spec A' ⟶ X ↦ (pullback q).obj K) hcomm) ≫
      (pullbackCompObjIso g' U'.2.fromSpec K).inv ≫
      (pullback U'.2.fromSpec).map α ≫
      (affineFunctor A').asEquivalence.counitIso.inv.app E')

/-- The two canonical arrows in the affine base-change comparison on a compatible chart. -/
noncomputable def canonicalAffineComparison
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :
    let U' := c.inducedU'
    AffineBaseChangeComparison
      (RingedSpace.sectionsRingOnOpen S.toRingedSpace c.V)
      (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
      (RingedSpace.sectionsRingOnOpen S'.toRingedSpace c.V')
      (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
      (f.appLE c.V c.U c.mapU) (g.appLE c.V c.V' c.mapV')
      (g'.appLE c.U U' inf_le_left) (f'.appLE c.V' U' inf_le_right)
      (affineLocalModel K c.U) (affineLocalModel K' U') :=
  let U' := c.inducedU'
  AffineBaseChangeComparison.of
    (RingedSpace.sectionsRingOnOpen S.toRingedSpace c.V)
    (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
    (RingedSpace.sectionsRingOnOpen S'.toRingedSpace c.V')
    (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
    (f.appLE c.V c.U c.mapU) (g.appLE c.V c.V' c.mapV')
    (g'.appLE c.U U' inf_le_left) (f'.appLE c.V' U' inf_le_right)
    (affineLocalModel K c.U) (affineLocalModel K' U')
    (affineChartFirstMapOf g' f' f g sq c.V c.U c.V' c.mapU c.mapV'
      (affineLocalModel K c.U))
    ((ModuleCat.derivedRestrictionOfScalars
      (f'.appLE c.V' U' inf_le_right).hom).map
        (canonicalAffineLinearMap K K' α c))

/-- The canonical affine comparison map is the composite of its two canonical arrows. -/
noncomputable def canonicalAffineComparisonMap
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :=
  (canonicalAffineComparison g' f' f g sq K K' α c).map

/-- Pointwise and affine comparison data for a cartesian square.  The public certified model
adds the localization data identifying these two presentations. -/
structure CohomologyBaseChangeComparison.{v}
    {X' X S' S : Scheme.{v}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) where
  pointModel : ∀ x' : X',
    DerivedBaseChangeModel (S.presheaf.stalk (f (g' x')))
      (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
      (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')
  pointTargetComparison : ∀ x' : X',
    (pointModel x').functor ⋙
        ModuleCat.derivedExtensionOfScalars (pointTensorMap g' f' f g sq x').hom ≅
      ModuleCat.derivedExtensionOfScalars (g'.stalkMap x').hom
  affinePullbackIso : ∀ (U : X.affineOpens) (V' : S'.affineOpens),
    affinePullbackSectionsFunctor g' f' U V' ≅
      affineTargetPullbackSectionsFunctor g' f' U V'

namespace CohomologyBaseChangeComparison

/-- Assemble the natural point and affine comparisons used by the cohomology base-change
criterion. -/
noncomputable def of
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (pointModel : ∀ x' : X',
      DerivedBaseChangeModel (S.presheaf.stalk (f (g' x')))
        (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
        (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x'))
    (pointTargetComparison : ∀ x' : X',
      (pointModel x').functor ⋙
          ModuleCat.derivedExtensionOfScalars (pointTensorMap g' f' f g sq x').hom ≅
        ModuleCat.derivedExtensionOfScalars (g'.stalkMap x').hom)
    (affinePullbackIso : ∀ (U : X.affineOpens) (V' : S'.affineOpens),
      affinePullbackSectionsFunctor g' f' U V' ≅
        affineTargetPullbackSectionsFunctor g' f' U V') :
    CohomologyBaseChangeComparison g' f' f g sq where
  pointModel := pointModel
  pointTargetComparison := pointTargetComparison
  affinePullbackIso := affinePullbackIso

/-- The pointwise derived comparison, formed from the strict realization of
`Kₓ ⊗ᴸ_R R'`, its canonical target-extension comparison, and the stalk map induced by `α`. -/
noncomputable def pointComparisonMap
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') :
    (ModuleCat.derivedExtensionOfScalars (pointTensorMap g' f' f g sq x').hom).obj
        ((D.pointModel x').functor.obj (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x'))) ⟶
      Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x' :=
  (D.pointTargetComparison x').hom.app
      (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')) ≫
    pointPullbackStalkMap g' K K' α x'

/-- The point comparison is the certified target isomorphism followed by the stalk map
induced by `α`. -/
theorem pointComparisonMap_spec
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') :
    D.pointComparisonMap K K' α x' =
      (D.pointTargetComparison x').hom.app
          (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')) ≫
        pointPullbackStalkMap g' K K' α x' := sorry

/-- The certified point-target comparison is natural in the stalk complex. -/
theorem pointTargetComparison_naturality
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq) (x' : X')
    {M N : DerivedCategory (ModuleCat (X.presheaf.stalk (g' x')))} (φ : M ⟶ N) :
    (((D.pointModel x').functor ⋙ ModuleCat.derivedExtensionOfScalars
        (pointTensorMap g' f' f g sq x').hom).map φ) ≫
          (D.pointTargetComparison x').hom.app N =
      (D.pointTargetComparison x').hom.app M ≫
        (ModuleCat.derivedExtensionOfScalars (g'.stalkMap x').hom).map φ := sorry

/-- The degree-`i` cohomology map attached to the pointwise derived base-change
realization. -/
noncomputable def pointCohomologyMap
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :=
  -- Local instance justification (noncanonical choice): the stalk map of `f` fixes the
  -- source-ring action used in the tensor-product coefficient ring.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the transported stalk map of `g`
  -- fixes the changed-base action in the tensor-product coefficient ring.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (S'.presheaf.stalk (f' x')) :=
    (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
  ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g sq x').hom
    ((D.pointModel x').functor.obj (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')))
    (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x')
    (D.pointComparisonMap K K' α x') i

/-- The point map is the cohomology base-change map formed from the
certified strict model and its comparison with the stalk of `α`. -/
theorem pointMap_spec
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :
    D.pointCohomologyMap K K' α x' i =
      let _ : Algebra (S.presheaf.stalk (f (g' x')))
          (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
      let _ : Algebra (S.presheaf.stalk (f (g' x')))
          (S'.presheaf.stalk (f' x')) :=
        (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
      ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g sq x').hom
        ((D.pointModel x').functor.obj (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')))
        (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x')
        (D.pointComparisonMap K K' α x') i := sorry

/-- The pointwise strict lift restricts to the canonical base-derived object
`Kₓ ⊗ᴸ_R R'`. -/
noncomputable def pointLiftRestrictionIso
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (x' : X') :=
  (D.pointModel x').objRestrictionIso
    (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x'))

/-- The displayed affine base-change comparison on a compatible chart. Its first arrow is the
derived pushout comparison, and its second arrow is induced by affine pullback and
`α`. -/
noncomputable def affine
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K')
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    AffineBaseChangeComparison
      (RingedSpace.sectionsRingOnOpen S.toRingedSpace V)
      (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)
      (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V')
      (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
      (f.appLE V U hU) (g.appLE V V' hV')
      (g'.appLE U U' inf_le_left) (f'.appLE V' U' inf_le_right)
      ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj
        ((ModuleDerived.Quasicoherent.inclusion X).obj K))
      ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').obj
        ((ModuleDerived.Quasicoherent.inclusion X').obj K')) :=
  let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
  AffineBaseChangeComparison.of
    (RingedSpace.sectionsRingOnOpen S.toRingedSpace V)
    (RingedSpace.sectionsRingOnOpen X.toRingedSpace U)
    (RingedSpace.sectionsRingOnOpen S'.toRingedSpace V')
    (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
    (f.appLE V U hU) (g.appLE V V' hV')
    (g'.appLE U U' inf_le_left) (f'.appLE V' U' inf_le_right)
    ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace U).obj
      ((ModuleDerived.Quasicoherent.inclusion X).obj K))
    ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').obj
      ((ModuleDerived.Quasicoherent.inclusion X').obj K'))
    (affineChartFirstMap g' f' f g sq K V U V' hU hV')
    ((D.affinePullbackIso U V').hom.app K ≫
      (ModuleCat.derivedRestrictionOfScalars
        (f'.appLE V' U' inf_le_right).hom).map
          ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').map
            ((ModuleDerived.Quasicoherent.inclusion X').map α)))

/-- The displayed affine comparison attached to a bundled compatible affine chart. -/
noncomputable def affineComparison
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :=
  D.affine K K' α c.V c.U c.V' c.mapU c.mapV'

/-- The affine map is the two canonical chartwise arrows composed on the chart. -/
theorem affineMap_spec
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :
    (D.affineComparison K K' α c).map =
      affineChartFirstMap g' f' f g sq K c.V c.U c.V' c.mapU c.mapV' ≫
        (D.affinePullbackIso c.U c.V').hom.app K ≫
          (ModuleCat.derivedRestrictionOfScalars
            (f'.appLE c.V'
              (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)) inf_le_right).hom).map
            ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace
              (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens))).map
                ((ModuleDerived.Quasicoherent.inclusion X').map α)) := sorry

/-- The first arrow of the affine comparison is the canonical derived pushout map. -/
theorem affine_toPullbackSections
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} {K : ModuleDerived.Quasicoherent X} {K' : ModuleDerived.Quasicoherent X'}
    {α : (pullback g').obj K ⟶ K'}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    (D.affine K K' α V U V' hU hV').toPullbackSections =
      affineChartFirstMap g' f' f g sq K V U V' hU hV' := sorry

/-- The second arrow of the affine comparison is the affine-pullback identification followed
by the map on derived sections induced by `α`. -/
theorem affine_toTargetSections
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} {K : ModuleDerived.Quasicoherent X} {K' : ModuleDerived.Quasicoherent X'}
    {α : (pullback g').obj K ⟶ K'}
    (D : CohomologyBaseChangeComparison g' f' f g sq)
    (V : S.affineOpens) (U : X.affineOpens) (V' : S'.affineOpens)
    (hU : U ≤ f ⁻¹ᵁ V) (hV' : V' ≤ g ⁻¹ᵁ V) :
    let U' := g' ⁻¹ᵁ (U : X.Opens) ⊓ f' ⁻¹ᵁ (V' : S'.Opens)
    (D.affine K K' α V U V' hU hV').toTargetSections =
      (D.affinePullbackIso U V').hom.app K ≫
        (ModuleCat.derivedRestrictionOfScalars
          (f'.appLE V' U' inf_le_right).hom).map
            ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').map
              ((ModuleDerived.Quasicoherent.inclusion X').map α)) := sorry

end CohomologyBaseChangeComparison

/-- A certified comparison model for cohomology and base change. It retains an
`𝒪_{X'}(U')`-linear lift of every displayed affine composite and localizes that lift
along `𝒪_{X'}(U') ⟶ 𝒪_{X',x'}` before comparing it with the point map. -/
structure CohomologyBaseChangeLocalizationModel.{v}
    {X' X S' S : Scheme.{v}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) where
  comparison : CohomologyBaseChangeComparison g' f' f g sq
  affineLinearComparison : ∀ (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g),
    let U' := g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)
    AffineTargetLinearComparison
      (RingedSpace.sectionsRingOnOpen S.toRingedSpace c.V)
      (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
      (RingedSpace.sectionsRingOnOpen S'.toRingedSpace c.V')
      (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
      (f.appLE c.V c.U c.mapU) (g.appLE c.V c.V' c.mapV')
      (g'.appLE c.U U' inf_le_left) (f'.appLE c.V' U' inf_le_right)
      ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace c.U).obj
        ((ModuleDerived.Quasicoherent.inclusion X).obj K))
      ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').obj
        ((ModuleDerived.Quasicoherent.inclusion X').obj K'))
      (comparison.affineComparison K K' α c)
  localizationFunctor : ∀ (c : AffineBaseChangeChart g' f' f g) (x' : X')
    (_ : x' ∈ (c.U' : X'.Opens)),
    DerivedCategory (ModuleCat
      (RingedSpace.sectionsRingOnOpen X'.toRingedSpace
        (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)))) ⥤
        DerivedCategory (ModuleCat (X'.presheaf.stalk x'))
  localizationFunctor_eq : ∀ (c : AffineBaseChangeChart g' f' f g) (x' : X')
    (hx' : x' ∈ (c.U' : X'.Opens)),
    localizationFunctor c x' hx' =
      ModuleCat.derivedExtensionOfScalars
        (X'.presheaf.germ
          (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)) x'
          (c.memPullback hx')).hom
  localizationSourceIso : ∀ (K : ModuleDerived.Quasicoherent X)
    (c : AffineBaseChangeChart g' f' f g) (x' : X')
    (hx' : x' ∈ (c.U' : X'.Opens)),
    let U' := g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)
    (localizationFunctor c x' hx').obj
        (affineTargetLinearSource
          (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
          (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
          (g'.appLE c.U U' inf_le_left)
          ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace c.U).obj
            ((ModuleDerived.Quasicoherent.inclusion X).obj K))) ≅
      (ModuleCat.derivedExtensionOfScalars
        (pointTensorMap g' f' f g sq x').hom).obj
          ((comparison.pointModel x').functor.obj
            (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')))
  localizationTargetIso : ∀ (K' : ModuleDerived.Quasicoherent X')
    (c : AffineBaseChangeChart g' f' f g) (x' : X')
    (hx' : x' ∈ (c.U' : X'.Opens)),
    let U' := g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)
    (localizationFunctor c x' hx').obj
        ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').obj
          ((ModuleDerived.Quasicoherent.inclusion X').obj K')) ≅
      Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x'
  localization_comm : ∀ (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g)
    (x' : X') (hx' : x' ∈ (c.U' : X'.Opens)),
    (localizationFunctor c x' hx').map
          ((affineLinearComparison K K' α c).map) ≫
        (localizationTargetIso K' c x' hx').hom =
      (localizationSourceIso K c x' hx').hom ≫
        comparison.pointComparisonMap K K' α x'

namespace CohomologyBaseChangeLocalizationModel

/-- Assemble a certified model from comparison data and its canonical localization square. -/
noncomputable def of
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    (comparison : CohomologyBaseChangeComparison g' f' f g sq)
    (affineLinearComparison : ∀ (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
      (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g),
      let U' := g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)
      AffineTargetLinearComparison
        (RingedSpace.sectionsRingOnOpen S.toRingedSpace c.V)
        (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
        (RingedSpace.sectionsRingOnOpen S'.toRingedSpace c.V')
        (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
        (f.appLE c.V c.U c.mapU) (g.appLE c.V c.V' c.mapV')
        (g'.appLE c.U U' inf_le_left) (f'.appLE c.V' U' inf_le_right)
        ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace c.U).obj
          ((ModuleDerived.Quasicoherent.inclusion X).obj K))
        ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').obj
          ((ModuleDerived.Quasicoherent.inclusion X').obj K'))
        (comparison.affineComparison K K' α c))
    (localizationFunctor : ∀ (c : AffineBaseChangeChart g' f' f g) (x' : X')
      (_ : x' ∈ (c.U' : X'.Opens)),
      DerivedCategory (ModuleCat
        (RingedSpace.sectionsRingOnOpen X'.toRingedSpace
          (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)))) ⥤
          DerivedCategory (ModuleCat (X'.presheaf.stalk x')))
    (localizationFunctor_eq : ∀ (c : AffineBaseChangeChart g' f' f g) (x' : X')
      (hx' : x' ∈ (c.U' : X'.Opens)),
      localizationFunctor c x' hx' =
        ModuleCat.derivedExtensionOfScalars
          (X'.presheaf.germ
            (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)) x'
            (c.memPullback hx')).hom)
    (localizationSourceIso : ∀ (K : ModuleDerived.Quasicoherent X)
      (c : AffineBaseChangeChart g' f' f g) (x' : X')
      (hx' : x' ∈ (c.U' : X'.Opens)),
      let U' := g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)
      (localizationFunctor c x' hx').obj
          (affineTargetLinearSource
            (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
            (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
            (g'.appLE c.U U' inf_le_left)
            ((RingedSpace.moduleDerivedSectionsAtOpen X.toRingedSpace c.U).obj
              ((ModuleDerived.Quasicoherent.inclusion X).obj K))) ≅
        (ModuleCat.derivedExtensionOfScalars
          (pointTensorMap g' f' f g sq x').hom).obj
            ((comparison.pointModel x').functor.obj
              (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x'))))
    (localizationTargetIso : ∀ (K' : ModuleDerived.Quasicoherent X')
      (c : AffineBaseChangeChart g' f' f g) (x' : X')
      (hx' : x' ∈ (c.U' : X'.Opens)),
      let U' := g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)
      (localizationFunctor c x' hx').obj
          ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace U').obj
            ((ModuleDerived.Quasicoherent.inclusion X').obj K')) ≅
        Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x')
    (localization_comm : ∀ (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
      (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g)
      (x' : X') (hx' : x' ∈ (c.U' : X'.Opens)),
      (localizationFunctor c x' hx').map
            ((affineLinearComparison K K' α c).map) ≫
          (localizationTargetIso K' c x' hx').hom =
        (localizationSourceIso K c x' hx').hom ≫
          comparison.pointComparisonMap K K' α x') :
    CohomologyBaseChangeLocalizationModel g' f' f g sq where
  comparison := comparison
  affineLinearComparison := affineLinearComparison
  localizationFunctor := localizationFunctor
  localizationFunctor_eq := localizationFunctor_eq
  localizationSourceIso := localizationSourceIso
  localizationTargetIso := localizationTargetIso
  localization_comm := localization_comm

/-- The canonical degree-`i` point map supplied by a certified model. -/
noncomputable def pointMap
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} (D : CohomologyBaseChangeLocalizationModel g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :=
  D.comparison.pointCohomologyMap K K' α x' i

/-- A certified model's point map is the cohomology map from its explicit strict model. -/
theorem pointMap_spec
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} (D : CohomologyBaseChangeLocalizationModel g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :
    D.pointMap K K' α x' i =
      let _ : Algebra (S.presheaf.stalk (f (g' x')))
          (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
      let _ : Algebra (S.presheaf.stalk (f (g' x')))
          (S'.presheaf.stalk (f' x')) :=
        (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
      ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g sq x').hom
        ((D.comparison.pointModel x').functor.obj
          (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')))
        (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x')
        (D.comparison.pointComparisonMap K K' α x') i := sorry

/-- The displayed affine comparison supplied by a certified model. -/
noncomputable def affineComparison
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} (D : CohomologyBaseChangeLocalizationModel g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :=
  D.comparison.affineComparison K K' α c

/-- A certified model's affine map is the two canonical chartwise arrows composed. -/
theorem affineMap_spec
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} (D : CohomologyBaseChangeLocalizationModel g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :
    (D.affineComparison K K' α c).map =
      affineChartFirstMap g' f' f g sq K c.V c.U c.V' c.mapU c.mapV' ≫
        (D.comparison.affinePullbackIso c.U c.V').hom.app K ≫
          (ModuleCat.derivedRestrictionOfScalars
            (f'.appLE c.V'
              (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens)) inf_le_right).hom).map
            ((RingedSpace.moduleDerivedSectionsAtOpen X'.toRingedSpace
              (g' ⁻¹ᵁ (c.U : X.Opens) ⊓ f' ⁻¹ᵁ (c.V' : S'.Opens))).map
                ((ModuleDerived.Quasicoherent.inclusion X').map α)) := sorry

end CohomologyBaseChangeLocalizationModel

/-- The canonical point and affine-local comparison maps attached to a cartesian square.
The affine datum retains both arrows of the derived tensor-product composite. -/
structure CohomologyBaseChangeModel.{v}
    {X' X S' S : Scheme.{v}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) where
  pointComparison : ∀ (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X'),
    (ModuleCat.derivedExtensionOfScalars (pointTensorMap g' f' f g sq x').hom).obj
        ((ModuleCat.derivedExtensionOfScalars
          (baseChangeRingLeftMap (S.presheaf.stalk (f (g' x')))
            (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
            (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')).hom).obj
              (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x'))) ⟶
      Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x'
  affineComparison : ∀ (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g),
    let U' := c.inducedU'
    AffineBaseChangeComparison
      (RingedSpace.sectionsRingOnOpen S.toRingedSpace c.V)
      (RingedSpace.sectionsRingOnOpen X.toRingedSpace c.U)
      (RingedSpace.sectionsRingOnOpen S'.toRingedSpace c.V')
      (RingedSpace.sectionsRingOnOpen X'.toRingedSpace U')
      (f.appLE c.V c.U c.mapU) (g.appLE c.V c.V' c.mapV')
      (g'.appLE c.U U' inf_le_left) (f'.appLE c.V' U' inf_le_right)
      (affineLocalModel K c.U) (affineLocalModel K' U')

namespace CohomologyBaseChangeModel

/-- The concrete canonical cohomology base-change model of a cartesian square. -/
noncomputable def canonical
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) :
    CohomologyBaseChangeModel g' f' f g sq where
  pointComparison := fun K K' α x' ↦
    canonicalPointComparisonMap g' f' f g sq K K' α x'
  affineComparison := fun K K' α c ↦
    canonicalAffineComparison g' f' f g sq K K' α c

/-- The degree-`i` pointwise cohomology map supplied by a comparison model. -/
noncomputable def pointMap
    {X' X S' S : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    {sq : IsPullback g' f' f g} (D : CohomologyBaseChangeModel g' f' f g sq)
    (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :=
  -- Local instance justification (noncanonical choice): the stalk map of `f` fixes the
  -- source-ring action used in the tensor-product coefficient ring.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (X.presheaf.stalk (g' x')) := (f.stalkMap (g' x')).hom.toAlgebra
  -- Local instance justification (noncanonical choice): the transported stalk map of `g`
  -- fixes the changed-base action in the tensor-product coefficient ring.
  let _ : Algebra (S.presheaf.stalk (f (g' x')))
      (S'.presheaf.stalk (f' x')) :=
    (baseChangeStalkMap g' f' f g sq x').hom.toAlgebra
  ModuleCat.cohomologyBaseChangeMap (pointTensorMap g' f' f g sq x').hom
    ((ModuleCat.derivedExtensionOfScalars
      (baseChangeRingLeftMap (S.presheaf.stalk (f (g' x')))
        (X.presheaf.stalk (g' x')) (S'.presheaf.stalk (f' x'))
        (f.stalkMap (g' x')) (baseChangeStalkMap g' f' f g sq x')).hom).obj
          (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X).obj K) (g' x')))
    (Stalk.obj ((ModuleDerived.Quasicoherent.inclusion X').obj K') x') (D.pointComparison K K' α x') i

/-- The canonical model's point map is the explicit cohomology base-change map. -/
theorem canonical_pointMap_spec
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (x' : X') (i : ℤ) :
    (canonical g' f' f g sq).pointMap K K' α x' i =
      canonicalPointCohomologyMap g' f' f g sq K K' α x' i := sorry

/-- The canonical model's affine datum is the two-arrow derived comparison on the chart. -/
theorem canonical_affineComparison_spec
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    (sq : IsPullback g' f' f g) (K : ModuleDerived.Quasicoherent X) (K' : ModuleDerived.Quasicoherent X')
    (α : (pullback g').obj K ⟶ K') (c : AffineBaseChangeChart g' f' f g) :
    (canonical g' f' f g sq).affineComparison K K' α c =
      canonicalAffineComparison g' f' f g sq K K' α c := sorry

end CohomologyBaseChangeModel

end AlgebraicGeometry.Scheme.DerivedQCoh

end
