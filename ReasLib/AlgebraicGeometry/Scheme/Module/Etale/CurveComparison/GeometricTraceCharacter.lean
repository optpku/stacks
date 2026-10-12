/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.DualSheafTracePairing
public import Mathlib.Algebra.Module.CharacterModule

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace ActualGeometricTraceCharacter
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


/-- The normalized embedding of degree modulo n into rational characters. -/
def normalizedCharacter : ZMod n →+ AddCircle (1 : ℚ) where
  toFun z := ↑((z.val : ℚ) / (n : ℚ))
  map_zero' := sorry
  map_add' := sorry

/-- The geometric compact-support class determines its actual trace character
on dual-sheaf cohomology. All maps precede the perfection theorem. -/
def traceCharacterMap (a b : ℕ) (hab : a + b = 2) :
    ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
      ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj F)).H a →+
    CharacterModule (((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj
      (ActualRootsHomCohomology.dualSheaf X n F)).H b) where
  toFun x :=
    { toFun := fun c ↦ normalizedCharacter n
        (ActualDualSheafTrace.pairing X C j n hpos hn F a b hab x c)
      map_zero' := sorry
      map_add' := sorry }
  map_zero' := sorry
  map_add' := sorry

/-- Poincare perfection for the specified normalized geometric evaluation.
The finite local coefficient, invertible n, smooth projective ambient curve,
and open immersion are retained. No group-cohomology comparison is an input. -/
theorem traceCharacterMap_bijective (a b : ℕ) (hab : a + b = 2) :
    Function.Bijective (traceCharacterMap X C j n hpos hn F a b hab) := sorry

/-- The inverse is determined by bijectivity of the constructed trace map. -/
def traceCharacterEquiv (a b : ℕ) (hab : a + b = 2) :
    ((etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj
      ((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj F)).H a ≃+
    CharacterModule (((ActualSiteExt.moduleForget X.left (ActualRootsModule.Coeff.{u} n)).obj
      (ActualRootsHomCohomology.dualSheaf X n F)).H b) :=
  AddEquiv.ofBijective (traceCharacterMap X C j n hpos hn F a b hab)
    (traceCharacterMap_bijective X C j n hpos hn F a b hab)

end ActualGeometricTraceCharacter
