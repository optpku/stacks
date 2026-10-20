/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Module.Quasicoherent
public import ReasLib.RingTheory.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ObjectProperty.Ind

@[expose] public section

open CategoryTheory
open SheafOfModules

universe u

namespace AlgebraicGeometry.GroupoidScheme.QCoh

open Scheme.Hom

/-- If the object and arrow schemes of a groupoid scheme are affine and global sections
on the arrow scheme are free over global sections on the object scheme via the source map,
then every equivariant quasi-coherent module is a small filtered colimit of equivariant
quasi-coherent modules whose underlying module sheaves are of finite type. -/
theorem isFiniteType_ind_of_sourceFree {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.U.left] [IsAffine G.R.left] (h_free : (appTop G.s.left).hom.Free)
    (F : G.QCoh) :
    ObjectProperty.ind.{u} (fun E : G.QCoh ↦ IsFiniteType E.obj.obj) F := sorry

end AlgebraicGeometry.GroupoidScheme.QCoh
