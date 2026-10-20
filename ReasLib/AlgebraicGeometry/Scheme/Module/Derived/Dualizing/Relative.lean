module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Monoidal.Mon
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.RelativeDualizingComplex

/-- The monoid object underlying the derived pushforward of the structure sheaf along a
scheme morphism. -/
noncomputable def diagonalAlgebra {X Y : Scheme.{u}} (δ : X ⟶ Y)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal] :
    Mon (RingedSpace.ModuleDerived Y.toRingedSpace) :=
  (RingedSpace.moduleDerivedPushforward δ.toShHom).mapMon.obj
    (Mon.trivial (RingedSpace.ModuleDerived X.toRingedSpace))

/-- The underlying object of `diagonalAlgebra δ` is the derived pushforward of the tensor
unit. -/
theorem diagonalAlgebra_obj {X Y : Scheme.{u}} (δ : X ⟶ Y)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal] :
    (diagonalAlgebra δ).X =
      (RingedSpace.moduleDerivedPushforward δ.toShHom).obj
        (𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace)) := sorry

/-- The internal-Hom map induced by multiplying the pushed-forward diagonal algebra and then
applying `ξ`. -/
noncomputable def dualityMap {X Y : Scheme.{u}} (δ : X ⟶ Y)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    {P : RingedSpace.ModuleDerived Y.toRingedSpace}
    (ξ : (diagonalAlgebra δ).X ⟶ P) :
    (diagonalAlgebra δ).X ⟶
      (MonoidalClosed.ihomOf H (diagonalAlgebra δ).X).obj P :=
  (MonoidalClosed.adjunctionOf H (diagonalAlgebra δ).X).homEquiv _ _
    ((diagonalAlgebra δ).mon.mul ≫ ξ)

/-- Uncurrying `dualityMap H ξ` recovers multiplication followed by `ξ`. -/
theorem dualityMap_spec {X Y : Scheme.{u}} (δ : X ⟶ Y)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived Y.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace))
    {P : RingedSpace.ModuleDerived Y.toRingedSpace}
    (ξ : (diagonalAlgebra δ).X ⟶ P) :
    ((MonoidalClosed.adjunctionOf H (diagonalAlgebra δ).X).homEquiv _ _).symm
        (dualityMap δ H ξ) =
      (diagonalAlgebra δ).mon.mul ≫ ξ := sorry

end AlgebraicGeometry.Scheme.RelativeDualizingComplex

namespace AlgebraicGeometry.Scheme

/-- A relative dualizing complex for `f : X ⟶ S`, relative to an open neighborhood `W` of
the diagonal and a closed factorization `δ : X ⟶ W.toScheme`, consists of an `S`-perfect
complex and the map whose induced internal-Hom morphism is invertible. -/
structure RelativeDualizingComplex {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)) where
  /-- The chosen derived `𝒪_X`-module. -/
  complex : RingedSpace.ModuleDerived X.toRingedSpace
  /-- The chosen map from `δ_*𝒪_X` to the pullback of `complex` along the first projection. -/
  map : (RelativeDualizingComplex.diagonalAlgebra δ).X ⟶
    (RingedSpace.modulePullbackDerived
      (W.ι ≫ pullback.fst f f).toShHom).obj complex
  /-- The chosen complex is perfect relative to `f`. -/
  isPerfect : ModuleDerived.IsPerfectRelativeTo f complex
  /-- The internal-Hom morphism induced by `map` is invertible. -/
  dualityMapIsIso : IsIso (RelativeDualizingComplex.dualityMap δ H map)

namespace RelativeDualizingComplex

/-- Construct a relative dualizing complex from its complex, map, and two defining
properties. -/
def of {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme) [IsClosedImmersion δ]
    (hδ : δ ≫ W.ι = pullback.diagonal f)
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    (H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (ξ : (diagonalAlgebra δ).X ⟶
      (RingedSpace.modulePullbackDerived
        (W.ι ≫ pullback.fst f f).toShHom).obj K)
    (hPerfect : ModuleDerived.IsPerfectRelativeTo f K)
    (hDuality : IsIso (dualityMap δ H ξ)) :
    RelativeDualizingComplex f W δ hδ H where
  complex := K
  map := ξ
  isPerfect := hPerfect
  dualityMapIsIso := hDuality

/-- The relative-perfectness and induced internal-Hom isomorphism defining a relative
dualizing complex. -/
theorem spec {X S : Scheme.{u}} {f : X ⟶ S}
    [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    {W : (pullback f f).Opens} {δ : X ⟶ W.toScheme} [IsClosedImmersion δ]
    {hδ : δ ≫ W.ι = pullback.diagonal f}
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)]
    [(RingedSpace.moduleDerivedPushforward δ.toShHom).LaxMonoidal]
    {H : MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)}
    (C : RelativeDualizingComplex f W δ hδ H) :
    ModuleDerived.IsPerfectRelativeTo f C.complex ∧
      IsIso (dualityMap δ H C.map) := sorry

/-- A flat, locally finitely presented morphism of schemes admits a relative dualizing
complex on an open neighborhood of its diagonal. -/
theorem existsRelativeDualizingComplex {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [monoidalX : MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)] :
    ∃ (W : (pullback f f).Opens) (δ : X ⟶ W.toScheme)
      (h_closed : IsClosedImmersion δ)
      (hδ : δ ≫ W.ι = pullback.diagonal f)
      (monoidalW : MonoidalCategory
        (RingedSpace.ModuleDerived W.toScheme.toRingedSpace))
      (laxPushforward : @CategoryTheory.Functor.LaxMonoidal
        (RingedSpace.ModuleDerived X.toRingedSpace) inferInstance monoidalX
        (RingedSpace.ModuleDerived W.toScheme.toRingedSpace) inferInstance monoidalW
        (RingedSpace.moduleDerivedPushforward δ.toShHom))
      (H : @MonoidalClosed (RingedSpace.ModuleDerived W.toScheme.toRingedSpace)
        inferInstance monoidalW),
      Nonempty (@Scheme.RelativeDualizingComplex X S f inferInstance inferInstance inferInstance W δ
        h_closed hδ monoidalX monoidalW laxPushforward H) := sorry

end RelativeDualizingComplex

end AlgebraicGeometry.Scheme
