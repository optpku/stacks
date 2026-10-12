/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal

/-!
# Normal sheaves of scheme morphisms

The normal sheaf of a scheme morphism is the internal-Hom dual of its conormal sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X : Scheme.{u}}

/-- The normal sheaf of a scheme morphism is the internal Hom from its conormal sheaf to the
structure sheaf of the source. -/
noncomputable abbrev normalSheaf (i : Z ⟶ X) : Z.Modules :=
  (ihom (conormalSheaf i)).obj (SheafOfModules.unit Z.ringCatSheaf)

end AlgebraicGeometry.Scheme.Hom
