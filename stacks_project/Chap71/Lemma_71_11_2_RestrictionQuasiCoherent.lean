/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap71.Lemma_71_11_2_RestrictionBaseChange
public import stacks_project.Chap71.Lemma_71_11_2_Quadruple

/-!
# The specified comparisons on quasi-coherent modules

The counit and pullback comparisons below are maps of the actual geometric
adjunctions. Invertibility is asserted only on quasi-coherent inputs.
-/

@[expose] public section
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.RelativeProj
open SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme
variable {S : Scheme.{u}} {T Z : Over S}

/-- The actual counit of extension/restriction is an isomorphism on QCoh. -/
instance counit_isIso (Z : Over S) (M : (ofOver Z).Modules) [M.IsQuasicoherent] :
    IsIso ((extensionAdjunction Z).counit.app M) := sorry

/-- The actual unit is an isomorphism on Zariski quasi-coherent modules. -/
instance unit_isIso (Z : Over S) (M : Z.left.Modules) [M.IsQuasicoherent] :
    IsIso ((extensionAdjunction Z).unit.app M) := sorry

/-- Extension of the Zariski pullback maps to the etale pullback by the counit. -/
def extensionPullbackComparison (t : T ⟶ Z) (M : (ofOver Z).Modules) :
    (extension T).obj ((Scheme.Modules.pullback t.left).obj
      ((Modules.restrictToScheme Z).obj M)) ⟶ (Modules.pullback (ofOverMap t)).obj M :=
  (extensionPullbackIso t).hom.app ((Modules.restrictToScheme Z).obj M) ≫
    (Modules.pullback (ofOverMap t)).map ((extensionAdjunction Z).counit.app M)

instance extensionPullbackComparison_isIso (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] : IsIso (extensionPullbackComparison t M) := sorry

/-- Restriction/pullback comparison is the adjoint of that specified map. -/
def pullbackComparison (t : T ⟶ Z) (M : (ofOver Z).Modules) :
    (Scheme.Modules.pullback t.left).obj ((Modules.restrictToScheme Z).obj M) ⟶
      (Modules.restrictToScheme T).obj ((Modules.pullback (ofOverMap t)).obj M) :=
  (extensionAdjunction T).homEquiv _ _ (extensionPullbackComparison t M)

/-- On QCoh this adjoint map is invertible, without an etale hypothesis on `t`. -/
instance pullbackComparison_isIso (t : T ⟶ Z) (M : (ofOver Z).Modules)
    [M.IsQuasicoherent] : IsIso (pullbackComparison t M) := sorry

/-- QCoh tensor powers restrict by the actual lax unit/tensor maps. -/
def tensorPowerComparison (Z : Over S) (L : (ofOver Z).Modules) (n : ℕ) :
    RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n ⟶
      (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) :=
  Nat.rec (unitMap Z)
    (fun k rec ↦ (𝟙 _ ⊗ₘ rec) ≫ tensorLax Z L (tensorPowerUnit L k)) n

instance tensorPowerComparison_isIso (Z : Over S) (L : (ofOver Z).Modules)
    [L.IsQuasicoherent] (n : ℕ) : IsIso (tensorPowerComparison Z L n) := sorry

/-- The tensor-power isomorphism inverts the specified restriction map. -/
def tensorPowerIso (Z : Over S) (L : (ofOver Z).Modules) [L.IsQuasicoherent] (n : ℕ) :
    RingedSpace.TensorPower.sheaf ((Modules.restrictToScheme Z).obj L) n ≅
      (Modules.restrictToScheme Z).obj (tensorPowerUnit L n) :=
  asIso (tensorPowerComparison Z L n)

/-- An invertible module on this small etale site is quasi-coherent. -/
theorem invertible_isQuasicoherent (Z : Over S) (L : (ofOver Z).Modules)
    (hL : isInvertibleObject L) : L.IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.RestrictToScheme

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj.DegreePieces

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}

/-- The supplied degree presentation inherits the original algebra's QCoh property. -/
theorem isQuasicoherent (deg : DegreePieces 𝒜) (hA : 𝒜.IsQuasicoherent) (n : ℕ) :
    (deg.obj n).IsQuasicoherent := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj.DegreePieces
