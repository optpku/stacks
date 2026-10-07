module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek.LocalDescription
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Remark 48.17.5 (Local description upper shriek): on compatible affine opens
`U ⊆ X` and `V ⊆ Y`, affine derived global sections identify the restriction of
`upperShriek f C M.plus` to `U` with the presentation-defined ring upper-shriek functor applied to the
affine model of the restriction of `E` to `V`. -/
@[stacks 0BV2] #check
  (AlgebraicGeometry.Scheme.Compactification.Of.upperShriekAffineRestrictionIsomorphic :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian S]
      {X Y : AlgebraicGeometry.Scheme.FiniteTypeSeparatedOver S} (f : X ⟶ Y)
      (C : AlgebraicGeometry.Scheme.Compactification.Of
        Y.obj.left (Over.mk f.hom.left))
      (M : AlgebraicGeometry.Scheme.DerivedQCoh.PlusRightAdjoint
        C.obj.right.hom)
      (U : AlgebraicGeometry.Scheme.affineOpens X.obj.left)
      (V : AlgebraicGeometry.Scheme.affineOpens Y.obj.left)
      (hUV : U ≤ f.hom.left ⁻¹ᵁ V)
      (p : ModuleCat.UpperShriek.Presentation
        (CommRingCat.Hom.hom
          (AlgebraicGeometry.Scheme.Hom.appLE f.hom.left V U hUV)))
      (E : AlgebraicGeometry.Scheme.DerivedQCoh.Plus Y.obj.left),
      IsIsomorphic
        ((AlgebraicGeometry.Scheme.Compactification.Of.upperShriek f C M.plus ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackPlus
            U.2.fromSpec ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsPlus
            Γ(X.obj.left, U) ⋙
          DerivedCategory.Plus.ι).obj E)
        (p.functor.obj
          ((AlgebraicGeometry.Scheme.DerivedQCoh.OpenImmersion.pullbackPlus
              V.2.fromSpec ⋙
            AlgebraicGeometry.Scheme.DerivedQCoh.affineGlobalSectionsPlus
              Γ(Y.obj.left, V) ⋙
            DerivedCategory.Plus.ι).obj E)))
