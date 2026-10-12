/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Monoidal.Adjunction.ProjectionFormula
public import stacks_project.Chap69.Lemma_69_4_3

/-!
# Lemma 69.4.4

For a finite morphism of algebraic spaces, the canonical derived projection-formula
mate of the associated morphism of ringed topoi is an isomorphism for arbitrary
objects of the derived categories of modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open CategoryTheory.Adjunction
open ComplexShape
open RingedSite.Hom RingedSite.ToposHom

noncomputable section

universe u uSite v w

namespace RingedSite.ToposHom

variable {X Y : RingedSite.{uSite, v, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- Module direct image along a morphism of ringed topoi is additive as a typeclass. -/
noncomputable instance modulePushforward.instAdditive (f : ToposHom X Y) :
    f.modulePushforward.Additive :=
  modulePushforward_additive f

variable [UnivLE.{max uSite v, w}]

/-- Absolute-derived pair conditions for the canonical ringed-topos module
adjunction. This is proof-only; the unit and counit are not supplied as data. -/
abbrev HasModuleDerivedAdjunction (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [HasModulePullbackDerived f] [HasModulePushforwardDerived f] : Prop :=
  @TotalDerived.HasPair
    (RingedSite.Hom.ModuleHomotopy.{w} Y) (RingedSite.Hom.ModuleHomotopy.{w} X)
    (RingedSite.Hom.ModuleDerived.{w} Y) (RingedSite.Hom.ModuleDerived.{w} X)
    inferInstance inferInstance inferInstance inferInstance
    (f.modulePullback.mapHomotopyCategory (up ℤ))
    (f.modulePushforward.mapHomotopyCategory (up ℤ))
    (RingedSite.Hom.ModuleQis.{w} Y) (RingedSite.Hom.ModuleQis.{w} X)
    (RingedSite.Hom.moduleLocalization.{w} Y) (RingedSite.Hom.moduleLocalization.{w} X)
    inferInstance inferInstance inferInstance inferInstance

/-- Derived inverse image is a left adjoint whenever `HasModuleDerivedAdjunction f` holds. -/
theorem hasModuleDerivedAdjunction_isLeftAdjoint (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [HasModulePullbackDerived f] [HasModulePushforwardDerived f]
    [HasModuleDerivedAdjunction f] :
    f.modulePullbackDerived.IsLeftAdjoint :=
  sorry

/-- The canonical derived pullback--pushforward adjunction, obtained by
deriving the explicit geometric/scalar module adjunction. -/
noncomputable def moduleDerivedAdjunction (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [HasModulePullbackDerived f] [HasModulePushforwardDerived f]
    [HasModuleDerivedAdjunction f] :
    f.modulePullbackDerived ⊣ f.modulePushforwardDerived :=
  TotalDerived.HasPair.derived
    (mapHomotopyCategoryAdjunction f.moduleAdjunction)
    (RingedSite.Hom.ModuleQis.{w} Y) (RingedSite.Hom.ModuleQis.{w} X)

/-- Transposing a morphism across `moduleDerivedAdjunction f` and back is the identity. -/
theorem moduleDerivedAdjunction_homEquiv_left_inv (f : ToposHom X Y)
    [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
    [HasModulePullbackDerived f] [HasModulePushforwardDerived f]
    [HasModuleDerivedAdjunction f]
    {K : ModuleDerived Y} {M : ModuleDerived X}
    (g : f.modulePullbackDerived.obj K ⟶ M) :
    ((moduleDerivedAdjunction f).homEquiv K M).symm
        ((moduleDerivedAdjunction f).homEquiv K M g) = g :=
  sorry

end RingedSite.ToposHom

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.4.4: let `S` be a scheme. Let `π : X ⟶ Y` be a finite morphism of algebraic
spaces over `S`. Let `A` be a sheaf of rings on `X_étale`. Let `B` be a sheaf of rings on
`Y_étale`. Let `φ : B ⟶ π_* A` be a homomorphism of sheaves of rings, so that we obtain a
morphism of ringed topoi `f = toRingedToposHom π φ`. For `K` in the derived category of
`B`-modules and `M` in the derived category of `A`-modules, the canonical map
`K ⊗ Rf_* M ⟶ Rf_*(Lf^* K ⊗ M)` is an isomorphism in `D(B)`. The smallness hypothesis
`UnivLE.{u + 1, u}` records that the étale sites are treated as small relative to the
coefficient universe, matching the Stacks Project's single-universe convention. -/
@[stacks 0DK5, instance]
instance IsFinite.derivedProjectionFormula
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (π : X ⟶ Y) [IsFinite π]
    (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (B : Sheaf (smallEtaleTopology Y) CommRingCat.{u})
    (φ : (etaleRingedSite Y B).structureSheaf ⟶
      (ringPushforward π).obj (etaleRingedSite X A).structureSheaf)
    [UnivLE.{u + 1, u}]
    [HasModulePullbackDerived (toRingedToposHom π φ)]
    [HasModulePushforwardDerived (toRingedToposHom π φ)]
    [HasModuleDerivedAdjunction (toRingedToposHom π φ)]
    [MonoidalCategory (ModuleDerived (etaleRingedSite Y B))]
    [MonoidalCategory (ModuleDerived (etaleRingedSite X A))]
    [Functor.Monoidal (toRingedToposHom π φ).modulePullbackDerived] :
    ((toRingedToposHom π φ).moduleDerivedAdjunction).ProjectionFormula :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
