module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.IdentityTarget
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Remark 37.9.6 (1): when the target thickening is `𝟙 Y`, every prescribed conormal
map is zero. -/
@[stacks 04FK] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.conormalMap_id_eq_zero :
    ∀ {X X' Y : AlgebraicGeometry.Scheme.{u}}
      (S : AlgebraicGeometry.Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
      [X.Over S] [X'.Over S] [Y.Over S]
      [AlgebraicGeometry.IsFirstOrderThickening i]
      [i.IsOver S] [a.IsOver S]
      (A : (AlgebraicGeometry.Scheme.Modules.pullback a).obj
          (AlgebraicGeometry.Scheme.Hom.conormalSheaf (𝟙 Y)) ⟶
        AlgebraicGeometry.Scheme.Hom.conormalSheaf i),
      A = 0)

/- Remark 37.9.6 (2): for the identity target thickening, local deformations are exactly
the `S`-morphisms whose restriction along `i` agrees with `a`. -/
@[stacks 04FK] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.sections_id :
    ∀ {X X' Y : AlgebraicGeometry.Scheme.{u}}
      (S : AlgebraicGeometry.Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
      [X.Over S] [X'.Over S] [Y.Over S]
      [AlgebraicGeometry.IsFirstOrderThickening i]
      [i.IsOver S] [a.IsOver S] (U' : X'.Opens),
      AlgebraicGeometry.Scheme.Hom.Deformation.sections S i (𝟙 Y) a 0 U' =
        {a' : U'.toScheme ⟶ Y |
          a' ≫ (Y ↘ S) = U'.ι ≫ (X' ↘ S) ∧
            (i ∣_ U') ≫ a' = (i ⁻¹ᵁ U').ι ≫ a})

section

variable {X X' Y : AlgebraicGeometry.Scheme.{u}}
variable (S : AlgebraicGeometry.Scheme.{u}) (i : X ⟶ X') (a : X ⟶ Y)
  [X.Over S] [X'.Over S] [Y.Over S]
  [AlgebraicGeometry.IsFirstOrderThickening i]
  [i.IsOver S] [a.IsOver S]

/- Remark 37.9.6 (3): the internal-Hom parameter sheaf acts on the specialized
deformation sheaf through its canonical pseudo-torsor. -/
@[stacks 04FK] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.pseudoTorsor S i (𝟙 Y) a 0 :
    CategoryTheory.Sheaf.PseudoTorsor
      (CategoryTheory.Sheaf.toSheafOfGroups
        (AlgebraicGeometry.Scheme.Hom.Deformation.parameterSheaf S i a)))

end
