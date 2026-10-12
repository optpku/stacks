/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Symmetric
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {Z X : Scheme.{u}}

/-- The conormal sheaf of an immersion is quasi-coherent. -/
theorem conormalSheaf_isQuasicoherent (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheaf i).IsQuasicoherent := sorry

/-- The conormal sheaf of an immersion carries its canonical quasi-coherence instance. -/
instance instIsQuasicoherentConormalSheaf (i : Z ⟶ X) [IsImmersion i] :
    (conormalSheaf i).IsQuasicoherent :=
  conormalSheaf_isQuasicoherent i

end AlgebraicGeometry.Scheme.Hom
