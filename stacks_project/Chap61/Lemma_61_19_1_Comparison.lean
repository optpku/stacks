/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleComparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u u₁ v₁

#check (AlgebraicGeometry.Scheme.etaleToProEt : (X : Scheme.{u}) → X.Etale ⥤ X.ProEt)
#check (AlgebraicGeometry.Scheme.etaleToProEtSheaf :
  (X : Scheme.{u}) → (A : Type u₁) → [Category.{v₁} A] →
    Sheaf (ProEt.topology X) A ⥤ Sheaf X.smallEtaleTopology A)
