module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FormalGlueing
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Lemma 81.10.2: the canonical two-term stalk comparison induces an isomorphism on kernels. -/
@[stacks 0AER] #check (AlgebraicGeometry.AlgebraicSpace.twoTermStalkComparison_kernel_isIso :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i]
    [AlgebraicGeometry.AlgebraicSpace.IsIntegralHom (AlgebraicGeometry.AlgebraicSpace.inverseImageTo f i)]
    [AlgebraicGeometry.AlgebraicSpace.UniversallyInjective (AlgebraicGeometry.AlgebraicSpace.inverseImageTo f i)]
    (ybar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint Y)
    (G : AlgebraicGeometry.AlgebraicSpace.EtaleSheaf Y),
    IsIso ((ker AddCommGrpCat.{u + 1}).map (AlgebraicGeometry.AlgebraicSpace.twoTermStalkComparison f i ybar G)))

/- Lemma 81.10.2: the canonical two-term stalk comparison induces a monomorphism on cokernels. -/
@[stacks 0AER] #check (AlgebraicGeometry.AlgebraicSpace.twoTermStalkComparison_cokernel_mono :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion i]
    [AlgebraicGeometry.AlgebraicSpace.IsIntegralHom (AlgebraicGeometry.AlgebraicSpace.inverseImageTo f i)]
    [AlgebraicGeometry.AlgebraicSpace.UniversallyInjective (AlgebraicGeometry.AlgebraicSpace.inverseImageTo f i)]
    (ybar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint Y)
    (G : AlgebraicGeometry.AlgebraicSpace.EtaleSheaf Y),
    Mono ((coker AddCommGrpCat.{u + 1}).map (AlgebraicGeometry.AlgebraicSpace.twoTermStalkComparison f i ybar G)))

