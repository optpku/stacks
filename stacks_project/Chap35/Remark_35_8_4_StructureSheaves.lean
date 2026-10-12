/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u v w

variable {C : Type w} [Category.{v} C]

/- This compatibility bridge re-exports the structure-sheaf API from its mathematical owner. -/
#check (AlgebraicGeometry.Scheme.Site.structurePresheaf :
  (C ⥤ Scheme.{u}) → Cᵒᵖ ⥤ RingCat.{u})
