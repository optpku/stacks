module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Smooth
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction.Etale
import StacksCheckRecall

/-!
# Reduction squares of smooth morphisms of formal algebraic spaces

A morphism of formal algebraic spaces representable by algebraic spaces and
smooth has cartesian reduction square, identifying
the reduction of `X` with the fibre product of `X` and the reduction of `Y` over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/- Lemma 87.12.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S` which is representable by algebraic spaces
and smooth (for example étale). Then the reduction of `X` is the fibre product
of `X` and the reduction of `Y` over `Y`, with its canonical maps. -/
@[stacks 0GB7] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.map_isPullback_of_smooth :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y),
      AlgebraicSpace.relativeAlgebraicSpaces
        (fun {_ _} g => AlgebraicSpace.Smooth g) f →
      IsPullback RX.ι (RX.map RY f) f RY.ι)

/- The reduction square of an étale morphism is cartesian. -/
#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.map_isPullback :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) [Etale f],
    IsPullback RX.ι (RX.map RY f) f RY.ι)

end AlgebraicGeometry.FormalAlgebraicSpace
