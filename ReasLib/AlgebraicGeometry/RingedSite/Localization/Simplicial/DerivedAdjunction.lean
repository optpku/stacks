/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Small

/-!
# Derived module adjunction for simplicial augmentations
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily (overSiteDiagram overSiteTotalTopology totalForget)

variable {X : RingedSite.{u, v, w}}

section Simplicial

variable (L : SimplicialObject (FormalCoproduct.{ι} X.carrier))
variable [UnivLE.{max ι u v, w}] [UnivLE.{max u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology L) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram L))ᵒᵖ ⥤ Type w,
    (totalForget L).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology L).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- Module pullback along a simplicial augmentation admits an unbounded total left
derived functor. -/
theorem toAmbient_hasModulePullbackDerived :
    ToposHom.HasModulePullbackDerived (toAmbient L) := sorry

/-- Module pushforward along a simplicial augmentation admits an unbounded total right
derived functor. -/
theorem toAmbient_hasModulePushforwardDerived :
    ToposHom.HasModulePushforwardDerived (toAmbient L) := sorry

/-- The module pullback and pushforward of a simplicial augmentation form an
absolute-derived adjoint pair. -/
theorem toAmbient_hasModuleDerivedAdjunction
    [ToposHom.HasModulePullbackDerived (toAmbient L)]
    [ToposHom.HasModulePushforwardDerived (toAmbient L)] :
    ToposHom.HasModuleDerivedAdjunction (toAmbient L) := sorry

/-- The unbounded derived inverse image along a simplicial augmentation. -/
def derivedPullback : Hom.ModuleDerived.{w} X ⥤ Hom.ModuleDerived.{w} (site L) :=
  @ToposHom.modulePullbackDerived _ _ inferInstance inferInstance (toAmbient L)
    inferInstance inferInstance inferInstance (toAmbient_hasModulePullbackDerived L)

/-- The unbounded derived direct image along a simplicial augmentation. -/
def derivedPushforward : Hom.ModuleDerived.{w} (site L) ⥤ Hom.ModuleDerived.{w} X :=
  @ToposHom.modulePushforwardDerived _ _ inferInstance inferInstance (toAmbient L)
    inferInstance inferInstance (toAmbient_hasModulePushforwardDerived L)

/-- The canonical derived inverse-image–direct-image adjunction of a simplicial
augmentation. -/
def derivedAdjunction : derivedPullback L ⊣ derivedPushforward L :=
  @ToposHom.moduleDerivedAdjunction _ _ inferInstance inferInstance (toAmbient L)
    inferInstance inferInstance inferInstance
    (toAmbient_hasModulePullbackDerived L) (toAmbient_hasModulePushforwardDerived L)
    (@toAmbient_hasModuleDerivedAdjunction _ L inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      (toAmbient_hasModulePullbackDerived L) (toAmbient_hasModulePushforwardDerived L))

/-- The functor on homotopy categories induced by module direct image along a
simplicial augmentation. -/
def modulePushforwardHomotopy : Hom.ModuleHomotopy.{w} (site L) ⥤ Hom.ModuleHomotopy.{w} X :=
  @Functor.mapHomotopyCategory _ _ _ _ _ _ _ (toAmbient L).modulePushforward
    (ToposHom.modulePushforward_additive (toAmbient L)) (ComplexShape.up ℤ)

end Simplicial

variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}] [UnivLE.{max u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/-- The canonical unit of derived module pullback and pushforward along a terminal
hypercovering augmentation. -/
def derivedUnit :
    𝟭 (Hom.ModuleDerived.{w} X) ⟶
      derivedPullback K.simplicial ⋙ derivedPushforward K.simplicial :=
  (derivedAdjunction K.simplicial).unit

end RingedSite.Localization.AtSimplicialSR
