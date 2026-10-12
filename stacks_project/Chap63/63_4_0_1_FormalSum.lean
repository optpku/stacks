/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteSupport

/-!
# Finite formal sums of étale sections with finite support
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

/- A source-facing compatibility import for downstream chapter statements. -/
#check (AlgebraicGeometry.Scheme.Etale.FiniteSupportFormalSum.sum :
  ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f]
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}} {V : Y.Etale} {n : ℕ},
    (Fin n → AlgebraicGeometry.Scheme.Etale.FiniteSupportTerm f F V) →
      AlgebraicGeometry.Scheme.Etale.FiniteSupportFormalSum f F V)

end
