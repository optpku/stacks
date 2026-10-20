module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective

/-! # Formal glueing comparison on abelian étale stalks -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The open complement immersion `j' : Y \ f⁻¹Z ⟶ Y`. -/
abbrev complementOpenImmersion {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    closedImmersionComplement (inverseImageι f i) ⟶ Y :=
  closedImmersionComplementι (inverseImageι f i)

/-- The adjunction unit `G ⟶ j'_*(j'⁻¹ G)` of restriction to the open complement of
`f⁻¹Z`. -/
def restrictUnit {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (G : EtaleSheaf Y) :
    G ⟶
      (sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G) :=
  (sheafAdjunction AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).unit.app G

/-- `restrictUnit` is the unit of `sheafAdjunction` at `G`. -/
theorem restrictUnit_eq {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (G : EtaleSheaf Y) :
    restrictUnit f i G =
      (sheafAdjunction AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).unit.app G :=
  rfl

/-- The source two-term complex
`(f_* G)_{ȳ.map f} ⟶ (f_* j'_*(j'⁻¹ G))_{ȳ.map f}`. -/
def sourceTwoTerm {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (etaleAbelianStalk (ybar.map f)).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G) ⟶
      (etaleAbelianStalk (ybar.map f)).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} f).obj
          ((sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
            ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G))) :=
  (etaleAbelianStalk (ybar.map f)).map
    ((sheafPushforward AddCommGrpCat.{u + 1} f).map (restrictUnit f i G))

/-- `sourceTwoTerm` is the stalk at `ȳ.map f` of `f_*` applied to `restrictUnit`. -/
theorem sourceTwoTerm_eq {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    sourceTwoTerm f i ybar G =
      (etaleAbelianStalk (ybar.map f)).map
        ((sheafPushforward AddCommGrpCat.{u + 1} f).map (restrictUnit f i G)) :=
  rfl

/-- The target two-term complex `G_ȳ ⟶ (j'_*(j'⁻¹ G))_ȳ`. -/
def targetTwoTerm {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (etaleAbelianStalk ybar).obj G ⟶
      (etaleAbelianStalk ybar).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
          ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G)) :=
  (etaleAbelianStalk ybar).map (restrictUnit f i G)

/-- `targetTwoTerm` is the stalk at `ȳ` of `restrictUnit`. -/
theorem targetTwoTerm_eq {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    targetTwoTerm f i ybar G = (etaleAbelianStalk ybar).map (restrictUnit f i G) :=
  rfl

/-- The canonical map of two-term complexes of abelian groups comparing pushforward
stalks at `ȳ.map f` with stalks at `ȳ`. -/
def twoTermStalkComparison {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    Arrow.mk (sourceTwoTerm f i ybar G) ⟶ Arrow.mk (targetTwoTerm f i ybar G) :=
  Arrow.homMk ((pushforwardStalkNatTrans f ybar).app G)
    ((pushforwardStalkNatTrans f ybar).app
      ((sheafPushforward AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} (complementOpenImmersion f i)).obj G)))
    ((pushforwardStalkNatTrans f ybar).naturality (restrictUnit f i G)).symm

/-- The two-term comparison is a commutative square. -/
theorem twoTermStalkComparison_w {X Y Z : AlgebraicSpace S} (f : Y ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (twoTermStalkComparison f i ybar G).left ≫ targetTwoTerm f i ybar G =
      sourceTwoTerm f i ybar G ≫ (twoTermStalkComparison f i ybar G).right :=
  Arrow.w (twoTermStalkComparison f i ybar G)

/-- The canonical comparison for restriction to the complement of an inverse-image closed
subspace induces an isomorphism on kernels when the morphism on that closed subspace
is integral and universally injective. -/
instance twoTermStalkComparison_kernel_isIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegralHom (inverseImageTo f i)] [UniversallyInjective (inverseImageTo f i)]
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    IsIso ((ker AddCommGrpCat.{u + 1}).map (twoTermStalkComparison f i ybar G)) :=
  sorry

/-- The canonical comparison for restriction to the complement of an inverse-image closed
subspace induces a monomorphism on cokernels when the morphism on that closed subspace
is integral and universally injective. -/
instance twoTermStalkComparison_cokernel_mono {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegralHom (inverseImageTo f i)] [UniversallyInjective (inverseImageTo f i)]
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    Mono ((coker AddCommGrpCat.{u + 1}).map (twoTermStalkComparison f i ybar G)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
