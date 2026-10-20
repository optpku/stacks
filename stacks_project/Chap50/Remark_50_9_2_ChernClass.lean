/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ChernClass

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {X S : Scheme.{u}}

#check (hodgeSource : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (p n : ℤ), Type u)
#check (hodgeCohomology : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (p q : ℕ), Type u)
#check (hodgeFiltrationStage : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n p : ℤ), Type u)
#check (ChernClassContext : ∀ {X S : Scheme.{u}} (f : X ⟶ S), Type (u + 1))
#check (gammaOne : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f)
  (L : X.Modules) [Scheme.Modules.Invertible L], hodgeSource f 1 2)
#check (gammaCupProduct : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (C : ChernClassContext f) {a : ℕ} (L : Fin a → X.Modules)
  [∀ i, Scheme.Modules.Invertible (L i)], hodgeSource f (a : ℤ) (2 * (a : ℤ)))
#check (hodgeMap_gammaOne : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f)
  (L : X.Modules) [Scheme.Modules.Invertible L],
  (hodgeMap f 1 2).hom (gammaOne f C L) =
    C.deRhamFirstChern (Scheme.Modules.picardClass L))
#check (hodgeProjection_gammaOne : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (C : ChernClassContext f) (L : X.Modules) [Scheme.Modules.Invertible L],
  C.hodgeProjection 1 (gammaOne f C L) =
    C.hodgeFirstChern (Scheme.Modules.picardClass L))
#check (hodgeMap_gammaCupProduct : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (C : ChernClassContext f) {a : ℕ} (L : Fin a → X.Modules)
  [∀ i, Scheme.Modules.Invertible (L i)],
  (hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (gammaCupProduct f C L) =
    C.deRhamCupProduct
      (fun i ↦ C.deRhamFirstChern (Scheme.Modules.picardClass (L i))))
#check (hodgeProjection_gammaCupProduct : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (C : ChernClassContext f) {a : ℕ} (L : Fin a → X.Modules)
  [∀ i, Scheme.Modules.Invertible (L i)],
  C.hodgeProjection a (gammaCupProduct f C L) =
    C.hodgeCupProduct
      (fun i ↦ C.hodgeFirstChern (Scheme.Modules.picardClass (L i))))

end AlgebraicGeometry.Scheme.DeRham
