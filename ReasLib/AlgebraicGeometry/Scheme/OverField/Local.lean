/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Local algebra of schemes over a field

This leaf supplies `Over (Spec k)` instance bridges for the neutral stalk and
residue-field algebra APIs of scheme morphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : Over (Spec (CommRingCat.of k)))

/-- The local ring at a point of the underlying scheme of an object over `Spec k`. -/
noncomputable abbrev stalkRing (x : X.left) :=
  X.left.presheaf.stalk x

/-- The structure morphism of a scheme over `Spec k` induces the canonical
`k`-algebra structure on the residue field at each point. -/
@[stacks 0C52]
noncomputable instance residueFieldAlgebra (x : X.left) :
    Algebra k (X.left.residueField x) :=
  Scheme.Hom.ResidueField.algebraOfSpec X.hom x

/-- The structure morphism of a scheme over `Spec k` induces the canonical
`k`-algebra structure on the local ring at each point. -/
@[stacks 035V]
noncomputable instance stalkAlgebra (x : X.left) :
    Algebra k (X.left.presheaf.stalk x) :=
  Scheme.Hom.stalkAlgebraOverField X.hom x

end AlgebraicGeometry.SchemeOverField
