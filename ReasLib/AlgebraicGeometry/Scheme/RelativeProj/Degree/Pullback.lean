/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Quadruple
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-! # The actual geometric pullback of a fixed-degree quadruple -/

@[expose] public section
open CategoryTheory AlgebraicGeometry
open SheafOfModules.RingedSite
noncomputable section
universe u

namespace AlgebraicGeometry.RelativeProjDegreeQuadruple

variable {S : Scheme.{u}} {𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf} {d : ℕ}

/-- Use the geometric presheaf core already specifying scheme-module inverse image. -/
def canonicalPullbackCore {T T' : Scheme.{u}} (g : T' ⟶ T) :
    Scheme.Modules.pullbackPresheafCore g :=
  RingedSpace.Hom.presheafCoreMonoidal g.toLRSHom.toShHom

/-- Pull back the actual adjoint homogeneous map, including the specified tensor comparison. -/
def canonicalPullbackHom {T T' : Scheme.{u}} (g : T' ⟶ T)
    (q : RelativeProjDegreeQuadruple 𝒜 d T) (n : ℕ) :
    (Scheme.Modules.pullback (g ≫ q.morphism)).obj (𝒜 (Int.ofNat (n * d))) ⟶
      RingedSpace.TensorPower.sheaf ((Scheme.Modules.pullback g).obj q.lineBundle) n :=
  (Scheme.Modules.pullbackComp g q.morphism).inv.app (𝒜 (Int.ofNat (n * d))) ≫
    (Scheme.Modules.pullback g).map
      (((Scheme.Modules.pullbackPushforwardAdjunction q.morphism).homEquiv
        (𝒜 (Int.ofNat (n * d))) (RingedSpace.TensorPower.sheaf q.lineBundle n)).symm
          (q.psi n)) ≫
    (pullbackTensorPowerIsoOf g (canonicalPullbackCore g) q.lineBundle n).hom

/-- The pushforward-form homogeneous map is obtained by the actual adjunction. -/
def canonicalPullbackPsi {T T' : Scheme.{u}} (g : T' ⟶ T)
    (q : RelativeProjDegreeQuadruple 𝒜 d T) (n : ℕ) :
    𝒜 (Int.ofNat (n * d)) ⟶
      (Scheme.Modules.pushforward (g ≫ q.morphism)).obj
        (RingedSpace.TensorPower.sheaf ((Scheme.Modules.pullback g).obj q.lineBundle) n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ q.morphism)).homEquiv _ _
    (canonicalPullbackHom (T := T) (T' := T') g q n)

/-- Pullback of a fixed-degree quadruple, with all object and morphism data computed. -/
def canonicalPullback {T T' : Scheme.{u}} (g : T' ⟶ T)
    (q : RelativeProjDegreeQuadruple 𝒜 d T) : RelativeProjDegreeQuadruple 𝒜 d T' where
  morphism := g ≫ q.morphism
  lineBundle := (Scheme.Modules.pullback g).obj q.lineBundle
  lineBundle_invertible := Scheme.Modules.Invertible.pullback g q.lineBundle_invertible
  psi := canonicalPullbackPsi (T := T) (T' := T') g q
  psi_map_one := sorry
  psi_map_mul := sorry
  degreeOneMap := canonicalPullbackHom (T := T) (T' := T') g q 1
  degreeOneMap_spec := rfl
  degreeOne_surjective := sorry

/-- The geometric specification uses this exact canonical core and the identity line comparison. -/
theorem canonicalPullback_spec {T T' : Scheme.{u}} (g : T' ⟶ T)
    (q : RelativeProjDegreeQuadruple 𝒜 d T) :
    IsPullbackAlong 𝒜 d g (canonicalPullbackCore g) q (canonicalPullback g q) (Iso.refl _) :=
  sorry

end AlgebraicGeometry.RelativeProjDegreeQuadruple
