/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.ZeroScheme
public import ReasLib.AlgebraicGeometry.BivariantClass.Commutation

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/-- The bivariant Gysin class of the zero scheme of a section of an invertible module
commutes with every bivariant class into the ambient scheme. -/
theorem gysin_commute
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {X Z : Over S} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Z.hom]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] (s : L.sections)
    (f : Z ⟶ X) [LocallyOfFiniteType f.left] (p : ℤ) (c : BivariantClass δ f p) :
    Commute δ f
      (Over.homMk (Scheme.zeroSchemeι L s) :
        Over.mk (Scheme.zeroSchemeι L s ≫ X.hom) ⟶ X)
      c (gysin δ X L s) := sorry

end AlgebraicGeometry.BivariantClass
