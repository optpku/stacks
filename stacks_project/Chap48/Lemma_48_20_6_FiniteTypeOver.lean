/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteTypeOver

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.FiniteTypeOver :
  ∀ (S : Scheme.{u}) [IsNoetherian S], Type (u + 1))

#check (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteType :
  ∀ {S : Scheme.{u}} [IsNoetherian S] (X : Scheme.FiniteTypeOver S),
    Scheme.Hom.FiniteType X.obj.hom)

#check (AlgebraicGeometry.Scheme.FiniteTypeOver.instIsNoetherian :
  ∀ {S : Scheme.{u}} [IsNoetherian S] (X : Scheme.FiniteTypeOver S),
    IsNoetherian X.obj.left)

#check (AlgebraicGeometry.Scheme.FiniteTypeOver.instFiniteTypeHom :
  ∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y),
    Scheme.Hom.FiniteType f.hom.left)

#check (AlgebraicGeometry.Scheme.FiniteTypeOver.condition :
  ∀ {S : Scheme.{u}} [IsNoetherian S] (X : Scheme.FiniteTypeOver S),
    Scheme.Hom.FiniteType X.obj.hom)

#check (AlgebraicGeometry.Scheme.FiniteTypeOver.hom_comm :
  ∀ {S : Scheme.{u}} [IsNoetherian S] {X Y : Scheme.FiniteTypeOver S} (f : X ⟶ Y),
    f.hom.left ≫ Y.obj.hom = X.obj.hom)
