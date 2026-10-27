/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Sites

/-! # Quasi-coherent modules on the étale, lisse-étale, and flat-fppf sites -/

open AlgebraicGeometry AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.AlgebraicStack CategoryTheory

universe u

/- Lemma 103.16.3: quasi-coherent modules on the étale site. -/
#check (AlgebraicGeometry.AlgebraicStack.etaleQuasiCoherent :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), ObjectProperty (etaleModules X))

#check (AlgebraicGeometry.AlgebraicStack.mem_etaleQCoh_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} (F : etaleModules X),
    etaleQuasiCoherent X F ↔ F.IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicStack.etaleQCoh :
  ∀ {S : Scheme.{u}}, GroupoidsOver S → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.etaleQCoh.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S), etaleQCoh X ⥤ etaleModules X)

/- Lemma 103.16.3: quasi-coherent modules on the lisse-étale site. -/
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleQuasiCoherent :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (SheafOfModules.{u} (lisseEtaleStructureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.mem_lisseEtaleQCoh_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : SheafOfModules.{u} (lisseEtaleStructureSheaf X)),
    lisseEtaleQuasiCoherent X F ↔ F.IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleQCoh.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    lisseEtaleQCoh X ⥤ SheafOfModules.{u} (lisseEtaleStructureSheaf X))

/- Lemma 103.16.3: quasi-coherent modules on the flat-fppf site. -/
#check (AlgebraicGeometry.AlgebraicStack.flatFppfQuasiCoherent :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    ObjectProperty (SheafOfModules.{u} (flatFppfStructureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.mem_flatFppfQCoh_iff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : SheafOfModules.{u} (flatFppfStructureSheaf X)),
    flatFppfQuasiCoherent X F ↔ F.IsQuasicoherent)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfQCoh :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfQCoh.inclusion :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    flatFppfQCoh X ⥤ SheafOfModules.{u} (flatFppfStructureSheaf X))
