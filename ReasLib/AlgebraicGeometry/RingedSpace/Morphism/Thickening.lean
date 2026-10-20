module

public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.RingTheory.Ideal.LocallyNilpotent

/-!
# Thickenings of ringed spaces

A morphism of ringed spaces is a thickening when the underlying map is a homeomorphism, the
structure-sheaf map is locally surjective, and the kernel ideal sheaf is locally nilpotent.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

namespace IdealSubobject

/-- A sheaf of ideals on a ringed space is locally nilpotent if every local section is locally
nilpotent. -/
def IsLocallyNilpotent {X : RingedSpace.{u}} (I : X.IdealSubobject) : Prop :=
  ∀ (U : Opens X) (s : X.presheaf.obj (op U)),
    s ∈ SheafOfModules.RingedSite.IdealSheaf.sections I (op U) →
      ∀ (x : X) (hx : x ∈ U), IsNilpotent (X.presheaf.germ U x hx s)

/-- Local nilpotence of an ideal sheaf is equivalent to local nilpotence of every stalk ideal. -/
theorem isLocallyNilpotent_iff {X : RingedSpace.{u}} (I : X.IdealSubobject) :
    I.IsLocallyNilpotent ↔
      ∀ x : X, (idealSheafStalkIdeal I x).IsLocallyNilpotent := sorry

end IdealSubobject

/-- A morphism of ringed spaces is a thickening if it is a homeomorphism on underlying spaces,
the structure-sheaf map is locally surjective, and the kernel ideal sheaf is locally nilpotent. -/
class IsThickening {X X' : RingedSpace.{u}} (i : X ⟶ X') : Prop where
  /-- The underlying continuous map is an isomorphism of topological spaces. -/
  base_isIso : IsIso i.hom.base
  /-- The structure-sheaf map `i^♯ : 𝒪_{X'} ⟶ i_* 𝒪_X` is locally surjective. -/
  c_locallySurjective : TopCat.Presheaf.IsLocallySurjective i.hom.c
  /-- The kernel of `i^♯` is a locally nilpotent sheaf of ideals. -/
  kernel_locallyNilpotent : (Hom.kernelIdealSubobject i).IsLocallyNilpotent

/-- A ringed-space morphism is a thickening iff it is a homeomorphism on spaces, has locally
surjective structure-sheaf map, and has locally nilpotent kernel ideal. -/
theorem isThickening_iff {X X' : RingedSpace.{u}} (i : X ⟶ X') :
    IsThickening i ↔
      IsIso i.hom.base ∧
        TopCat.Presheaf.IsLocallySurjective i.hom.c ∧
          (Hom.kernelIdealSubobject i).IsLocallyNilpotent := sorry

/-- The identity morphism of a ringed space is a thickening. -/
instance IsThickening.id (X : RingedSpace.{u}) : IsThickening (𝟙 X) := sorry

/-- The underlying map of a thickening of ringed spaces is a homeomorphism. -/
theorem IsThickening.isHomeomorph_base {X X' : RingedSpace.{u}} (i : X ⟶ X')
    [IsThickening i] : IsHomeomorph i.hom.base := sorry

/-- The category of ringed-space thickenings, with commutative squares as morphisms. -/
abbrev Thickening :=
  MorphismProperty.Arrow (@IsThickening : MorphismProperty RingedSpace.{u}) ⊤ ⊤

namespace Thickening

/-- Construct a bundled thickening from a ringed-space morphism carrying the thickening
property. -/
def of {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsThickening i] : Thickening.{u} :=
  MorphismProperty.Arrow.mk i (inferInstance : IsThickening i)

/-- The defining morphism of a bundled thickening constructed by `Thickening.of`. -/
theorem of_hom {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsThickening i] :
    (of i).hom = i := sorry

/-- Construct a morphism of thickenings from its maps on the closed spaces and ambient
spaces, together with their commutative-square equation. -/
def homMk {T U : Thickening.{u}} (f : T.left ⟶ U.left) (f' : T.right ⟶ U.right)
    (w : f ≫ U.hom = T.hom ≫ f') : T ⟶ U :=
  MorphismProperty.Arrow.homMk f f' w

/-- The map on closed spaces of a morphism constructed by `Thickening.homMk`. -/
theorem homMk_left {T U : Thickening.{u}} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') :
    (homMk f f' w).left = f := sorry

/-- The map on ambient spaces of a morphism constructed by `Thickening.homMk`. -/
theorem homMk_right {T U : Thickening.{u}} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') :
    (homMk f f' w).right = f' := sorry

/-- The kernel ideal sheaf of a bundled thickening: `ℐ = Ker(i^♯)` on the source and
`𝒥 = Ker(t^♯)` on the target. -/
noncomputable abbrev ker (T : Thickening.{u}) : T.right.IdealSubobject :=
  Hom.kernelIdealSubobject T.hom

namespace Hom

/-- The commutative-square equation satisfied by a morphism of thickenings. -/
theorem w {T U : Thickening.{u}} (g : T ⟶ U) :
    g.left ≫ U.hom = T.hom ≫ g.right := sorry

/-- A morphism of thickenings is a commutative square of ringed spaces. -/
theorem toCommSq {T U : Thickening.{u}} (g : T ⟶ U) :
    CommSq T.hom g.left g.right U.hom := sorry

set_option maxHeartbeats 800000 in
/-- The pulled-back kernel `(f')^* 𝒥` factors through `ℐ = Ker(i^♯)` as subobjects of
`𝒪_{X'}`. -/
theorem idealMap_factors {T U : Thickening.{u}} (g : T ⟶ U) :
    (ker T).Factors ((ker U).pullbackMap g.right) := by
  apply CategoryTheory.Limits.kernelSubobject_factors
  apply (RingedSpace.Hom.pullbackPushforwardAdjunction g.right).homEquiv _ _ |>.injective
  simp only [IdealSubobject.pullbackMap, Category.assoc]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [RingedSpace.Hom.pullbackPushforwardAdjunction,
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_zero]
  ext openSet localSection
  change T.hom.hom.c.app _
    (g.right.hom.c.app openSet ((ker U).arrow.val.app openSet localSection)) = 0
  have killed : U.hom.hom.c.app openSet
      ((ker U).arrow.val.app openSet localSection) = 0 := by
    exact congrArg (fun morphism => (morphism.val.app openSet).hom localSection)
      (CategoryTheory.Limits.kernelSubobject_arrow_comp
        (SheafOfModules.RingedSite.KernelIdeal.map
          (RingedSpace.Hom.commRingSheafPushforwardMap U.hom)))
  have square := SheafedSpace.congr_hom_app
    (MorphismProperty.Arrow.w g).symm openSet
  rw [SheafedSpace.comp_hom_c_app, SheafedSpace.comp_hom_c_app] at square
  have evaluated := ConcreteCategory.congr_hom square
    ((ker U).arrow.val.app openSet localSection)
  change T.hom.hom.c.app _
      (g.right.hom.c.app openSet ((ker U).arrow.val.app openSet localSection)) =
    T.left.presheaf.map _ (g.left.hom.c.app _
      (U.hom.hom.c.app openSet ((ker U).arrow.val.app openSet localSection))) at evaluated
  rw [killed] at evaluated
  exact evaluated.trans (by
    change (T.left.presheaf.map _).hom
      ((g.left.hom.c.app ((Opens.map U.hom.hom.base).op.obj openSet)).hom 0) = 0
    simp only [map_zero]
    exact map_zero _)

/-- The comparison `(f')^* 𝒥 ⟶ ℐ` induced by `(f')^♯` on the target kernel. -/
noncomputable def idealMap {T U : Thickening.{u}} (g : T ⟶ U) :
    (RingedSpace.Hom.pullback g.right).obj (ker U).toModule ⟶ (ker T).toModule :=
  (ker T).factorThru ((ker U).pullbackMap g.right) (idealMap_factors g)

/-- The comparison `(f')^* 𝒥 ⟶ ℐ` followed by the inclusion of `ℐ` recovers
`(f')^* 𝒥 ⟶ 𝒪_{X'}`. -/
theorem idealMap_arrow {T U : Thickening.{u}} (g : T ⟶ U) :
    idealMap g ≫ (ker T).arrow = (ker U).pullbackMap g.right := sorry

/-- The inverse-image ideal `(f')^{-1} 𝒥` is contained in `ℐ = Ker(i^♯)`. -/
theorem idealMap_le {T U : Thickening.{u}} (g : T ⟶ U) :
    (ker U).pullback g.right ≤ ker T := sorry

end Hom

end Thickening

end AlgebraicGeometry.RingedSpace
