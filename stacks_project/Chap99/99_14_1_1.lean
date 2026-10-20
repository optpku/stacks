module

public import ReasLib.AlgebraicGeometry.Polarized.ToSpaces
import StacksCheckRecall

/-!
# The forgetful functor from Polarized to Spaces'_{fp, flat, proper}
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p

noncomputable section

universe u

/- 99.14.1.1: the forgetful construction sends a polarized proper flat
finitely presented scheme family `(X ⟶ S, L)` to its underlying family
`(X ⟶ S)` in `Spaces'_{fp, flat, proper}`, retaining the cartesian square on
morphisms and forgetting the line-bundle isomorphism. -/
@[stacks 0D3Y] #check
  (AlgebraicGeometry.Polarized.toFpFlatProper :
    AlgebraicGeometry.Polarized.Obj.{u} ⥤
      AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
        (⊤_ AlgebraicGeometry.Scheme.{u}))

#check
  (AlgebraicGeometry.Polarized.toFpFlatProper_obj :
    ∀ (x : AlgebraicGeometry.Polarized.Obj.{u}),
      AlgebraicGeometry.Polarized.toFpFlatProper.obj x =
        AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids.mk
          (AlgebraicGeometry.Polarized.toHom x))

#check
  (AlgebraicGeometry.Polarized.toFpFlatProper_map :
    ∀ {x y : AlgebraicGeometry.Polarized.Obj.{u}} (φ : x ⟶ y),
      AlgebraicGeometry.Polarized.toFpFlatProper.map φ =
        AlgebraicGeometry.Polarized.toFpFlatProperHom φ)
