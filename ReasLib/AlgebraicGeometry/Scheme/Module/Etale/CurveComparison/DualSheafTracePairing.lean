/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.RootsHomCohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NormalizedYonedaTrace
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualDualSheafTrace
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
variable (j : X.left ⟶ C.left) [IsOpenImmersion j]
variable (n : ℕ) (hpos : 0 < n) (hn : IsUnit (n : k))
variable [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n))]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [X.left.smallEtaleTopology.HasSheafCompose
    (forget₂ (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [EnoughInjectives (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasSheafify C.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf C.left.smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleRestriction j).op.HasLeftKanExtension G]
variable (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} n)))
variable [Sheaf.IsFiniteTypeLocallyConstantModule F]

/-- Forgetting the displayed Z/n action returns precisely the same roots sections. -/
def rootsForgetIso :
    (ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj (ActualRootsModule.liftedSheaf X.left n) ≅
      ActualRootsModule.additiveSheaf X.left n where
  hom := ObjectProperty.homMk
    { app := fun _ ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
      naturality := sorry }
  inv := ObjectProperty.homMk
    { app := fun _ ↦ AddCommGrpCat.ofHom (AddMonoidHom.id _)
      naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

instance extension_additive : (etaleExtensionByZero j AddCommGrpCat.{u + 1}).Additive := sorry
instance extension_preservesFiniteLimits :
    PreservesFiniteLimits (etaleExtensionByZero j AddCommGrpCat.{u + 1}) := sorry
instance extension_preservesFiniteColimits :
    PreservesFiniteColimits (etaleExtensionByZero j AddCommGrpCat.{u + 1}) := sorry

/-- Actual cohomology of the dual sheaf maps to the trace's Ext input:
resolve μ_n in Z/n modules, forget scalars exactly, identify the same roots
sections, and apply exact extension by zero to the Yoneda class. -/
def dualCohomologyToCompactExt (i : ℕ)
    (c : ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj
      (ActualRootsHomCohomology.dualSheaf X n F)).H i) :
    Ext ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
        ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj F))
      (SchemeOverField.NormalizedCurveTrace.intrinsicCompactRootsSheaf C j n) i :=
  let e := (ActualRootsHomCohomology.cohomologyExtIso X n hpos hn F i).hom c
  let e' := (e.mapExactFunctor (ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n))).comp
    (Ext.mk₀ (rootsForgetIso X n).hom) (Nat.add_zero i)
  e'.mapExactFunctor (etaleExtensionByZero j AddCommGrpCat.{u + 1})

/-- The normalized geometric pairing, using actual dual-sheaf cohomology
as its second input and the specified Kummer/Yoneda trace as its value. -/
def pairing (a b : ℕ) (hab : a + b = 2)
    (x : ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
      ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj F)).H a)
    (c : ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj
      (ActualRootsHomCohomology.dualSheaf X n F)).H b) : ZMod n :=
  SchemeOverField.NormalizedCurveTrace.yonedaCompactTrace C j n hpos hn
    ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj F) a b hab x
    (dualCohomologyToCompactExt X C j n hpos hn F b c)

end ActualDualSheafTrace
