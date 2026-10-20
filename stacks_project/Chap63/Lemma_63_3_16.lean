module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.Coproduct
import StacksCheckRecall

/-!
# Compact-support pushforward preserves direct sums
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u v

/- Lemma 63.3.16: if `f : X ⟶ Y` is a morphism of schemes which is separated
and locally of finite type, then the functor `etaleLowerShriek f` commutes with
direct sums. -/
@[stacks 0F56] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriek_preservesCoproducts :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f]
      {I : Type v},
      PreservesColimitsOfShape (Discrete I)
        (AlgebraicGeometry.Scheme.Etale.etaleLowerShriek f))
