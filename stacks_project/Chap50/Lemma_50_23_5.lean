/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.Cohomology
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory RingedSpace
open SheafOfModules.RingedSite.ExteriorPower

noncomputable section

universe u

/- Lemma 50.23.5: for `α ∈ H^q(X, Ω^p_{X/S})`, the Gysin image
`γ^p(α|Z)` equals `i⁻¹α ∧ γ⁰(1)` in the degree-`q` cohomology of
`H^c_Z(Ω^(p+c)_{X/S})`. -/
@[stacks 0G88] #check
  (AlgebraicGeometry.Scheme.DeRham.Gysin.cohomologyMap_restriction :
    ∀ {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p q : ℕ)
      [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
      (α : RingedSpace.moduleCohomology
        ((Scheme.Modules.toRingedSpace X).obj (sheaf X.𝒪 Ω[f.toShHom] p)) q),
      (AlgebraicGeometry.Scheme.DeRham.Gysin.cohomologyMap i f c p q).hom
          ((AlgebraicGeometry.Scheme.DeRham.Gysin.restriction i f p q).hom α) =
        (AlgebraicGeometry.Scheme.DeRham.Gysin.wedgeFundamentalClass i f c p q).hom α)

end
