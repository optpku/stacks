module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Objects
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.OpenSubschemes

/-!
# Birationality via Generic-Point Stalks

This file characterizes birationality of irreducible schemes locally of finite
presentation over a base by compatible isomorphisms of their generic-point stalks.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Birationality over `S` via the generic-point schemes is equivalent to the existence of a
common image and a generic-point stalk isomorphism compatible with the two maps from the
transported stalk of `S`. -/
theorem birationalOver_iff_exists_genericPointStalkIso
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y] :
    BirationalOver S X Y ↔
      ∃ (s : S) (hx : (X ↘ S) (genericPoint X) = s) (hy : (Y ↘ S) (genericPoint Y) = s)
        (e : X.presheaf.stalk (genericPoint X) ≅ Y.presheaf.stalk (genericPoint Y)),
          ((S.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫
              (X ↘ S).stalkMap (genericPoint X)) ≫ e.hom =
            (S.presheaf.stalkCongr (.of_eq hy.symm)).hom ≫
              (Y ↘ S).stalkMap (genericPoint Y) := sorry

namespace Scheme

/-- For irreducible schemes locally of finite presentation over `S`, birationality over `S`,
isomorphic nonempty open subschemes over `S`, and compatible isomorphism of the generic-point
stalks are equivalent. -/
theorem birationalOver_tfae_of_locallyOfFinitePresentation
    (S X Y : Scheme.{u}) [X.Over S] [Y.Over S]
    [IrreducibleSpace X] [IrreducibleSpace Y]
    [LocallyOfFinitePresentation (X ↘ S)] [LocallyOfFinitePresentation (Y ↘ S)] :
    List.TFAE
      [ Scheme.BirationalOver (X ↘ S) (Y ↘ S)
      , HasIsomorphicNonemptyOpenSubschemesOver S X Y
      , AlgebraicGeometry.BirationalOver S X Y
      ] := sorry

end Scheme

end AlgebraicGeometry
