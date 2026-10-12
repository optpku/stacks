/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
import ReasLib.AlgebraicGeometry.Scheme.Morphism.SchemeTheoreticImage.StrictTransform
import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.OpenImmersion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- A chosen compactification of a quasi-compact open in a separated finite-type scheme
admits an admissible blowup with an open neighborhood on which the inclusion extends to a
proper morphism. -/
theorem exists_isAdmissibleBlowup_properExtension
    {S U : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : U ⟶ S) [Scheme.Hom.FiniteType f] [IsSeparated f]
    (V : U.Opens) [QuasiCompact V.ι]
    (P : Of S (Over.mk (V.ι ≫ f))) :
    ∃ (Y' : Scheme.{u}) (b : Y' ⟶ P.obj.right.left),
      IsAdmissibleBlowup (Of.ι P).opensRange b ∧
        ∃ (V' : Y'.Opens) (j : V.toScheme ⟶ V'.toScheme)
          (g : V'.toScheme ⟶ U),
          IsOpenImmersion j ∧
            j ≫ V'.ι ≫ b = Of.ι P ∧
              IsProper g ∧
                j ≫ g = V.ι := sorry

end AlgebraicGeometry.Scheme.Compactification
