module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CotangentComplex.FibreProduct
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace.Cotangent
open AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct

universe u

/- 92.28.0.1: For arbitrary morphisms X ⟶ B and Y ⟶ B of algebraic spaces over
S, the two transitivity triangles on W = X ×_B Y extend to the commuting
fibre-product diagram. Its upper-right object is the cone of the sum of the
canonical first maps. Compatible completion and connecting arrows make both
the top row and the right column distinguished. -/
@[stacks 09DK]
#check (AlgebraicGeometry.AlgebraicSpace.Cotangent.FibreProduct.diagram :
  ∀ {S : Scheme.{u}} {B X Y : AlgebraicSpace S} (f : X ⟶ B) (g : Y ⟶ B),
    let p := pullback.fst f g
    let q := pullback.snd f g
    let t := DerivedCategory.Q.map (cotangentToBaseIso f g).inv
    ∃ (a : cotangent q ⟶ cone f g) (b : cotangent p ⟶ cone f g)
      (dp : cotangent p ⟶ (pullbackCotangent p f)⟦(1 : ℤ)⟧)
      (dq : cotangent q ⟶ (pullbackCotangent q g)⟦(1 : ℤ)⟧)
      (dt : cone f g ⟶ (pullbackCotangent p f)⟦(1 : ℤ)⟧)
      (dr : cone f g ⟶ (pullbackCotangent q g)⟦(1 : ℤ)⟧),
      Triangle.mk (transitivityMap p f) (toRelativeMap p f) dp ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      Triangle.mk (transitivityMap q g ≫ DerivedCategory.Q.map (cotangentToBaseIso f g).hom)
        (t ≫ toRelativeMap q g) dq ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      Triangle.mk (topMap f g) a dt ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      Triangle.mk (rightMap f g) b dr ∈
        distTriang (DerivedCategory (CommModules (pullback f g))) ∧
      t ≫ toRelativeMap q g ≫ a = coneInr f g ∧
      toRelativeMap p f ≫ b = coneInr f g)
