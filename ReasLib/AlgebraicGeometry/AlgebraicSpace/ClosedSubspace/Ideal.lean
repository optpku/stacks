/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.MorphismProperty.Representable.MonoDiagonal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSheaf

/-!
# Closed subspaces cut out by ideal sheaves

A quasi-coherent ideal sheaf `I ⊂ 𝒪_X` cuts out a closed subspace of an
algebraic space `X`. Scheme-theoretic intersection and union of closed
subspaces are the closed subspaces cut out by `I ⊔ J` and `I ⊓ J`.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The morphism `ofOver T.unop ⟶ X` determined by a `T`-point of `X`. -/
def homOfPoint {T : (Over S)ᵒᵖ} (h : X.functorOfPoints.obj T) :
    ofOver T.unop ⟶ X :=
  yonedaEquiv.symm h

/-- `homOfPoint` is the Yoneda inverse of a `T`-point. -/
theorem homOfPoint_eq {T : (Over S)ᵒᵖ} (h : X.functorOfPoints.obj T) :
    homOfPoint h = yonedaEquiv.symm h :=
  rfl

/-- The pullback of the inclusion of an ideal sheaf along a morphism of algebraic
spaces. -/
def inclusionPullback {Y : AlgebraicSpace S} (f : Y ⟶ X) (I : IdealSubobject X) :
    (Modules.pullback f).obj I.toModule ⟶
      (Modules.pullback f).obj (SheafOfModules.unit (structureSheaf X)) :=
  (Modules.pullback f).map I.arrow

/-- `inclusionPullback f I` is the image of the subobject arrow of `I` under
module pullback along `f`. -/
theorem inclusionPullback_eq {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (I : IdealSubobject X) :
    inclusionPullback f I = (Modules.pullback f).map I.arrow :=
  rfl

/-- A morphism `f : Y ⟶ X` vanishes on an ideal sheaf `I` when the pulled-back
inclusion `f* I ⟶ f* 𝒪_X` is the zero map. -/
def vanishes {Y : AlgebraicSpace S} (f : Y ⟶ X) (I : IdealSubobject X) : Prop :=
  inclusionPullback f I = 0

/-- Vanishing of `I` along `f` is vanishing of the pulled-back inclusion of `I`. -/
theorem vanishes_iff {Y : AlgebraicSpace S} (f : Y ⟶ X) (I : IdealSubobject X) :
    vanishes f I ↔ inclusionPullback f I = 0 :=
  Iff.rfl

/-- Restriction of a `T`-point along a morphism of test schemes preserves
vanishing of a pulled-back ideal sheaf. -/
theorem vanishes_map {T T' : (Over S)ᵒᵖ} (φ : T ⟶ T') (I : IdealSubobject X)
    {h : X.functorOfPoints.obj T} (hh : vanishes (homOfPoint h) I) :
    vanishes (homOfPoint (X.functorOfPoints.map φ h)) I :=
  sorry

/-- Functor of points of the closed subspace of `X` cut out by an ideal sheaf:
`T`-points are morphisms `T ⟶ X` along which the pulled-back inclusion of the
ideal vanishes. -/
def subschemeFunctor (I : IdealSubobject X) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {h : X.functorOfPoints.obj T // vanishes (homOfPoint h) I}
  map φ := TypeCat.ofHom fun h => ⟨X.functorOfPoints.map φ h.val, vanishes_map φ I h.property⟩
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro h
    apply Subtype.ext
    change X.functorOfPoints.map (𝟙 T) h.val = h.val
    rw [X.functorOfPoints.map_id]
    rfl
  map_comp φ ψ := by
    apply ConcreteCategory.hom_ext
    intro h
    apply Subtype.ext
    change X.functorOfPoints.map (φ ≫ ψ) h.val =
      X.functorOfPoints.map ψ (X.functorOfPoints.map φ h.val)
    rw [X.functorOfPoints.map_comp]
    rfl

/-- The value of `subschemeFunctor I` at a test object is the subtype of points
along which `I` vanishes. -/
theorem subschemeFunctor_obj (I : IdealSubobject X) (T : (Over S)ᵒᵖ) :
    (subschemeFunctor I).obj T =
      {h : X.functorOfPoints.obj T // vanishes (homOfPoint h) I} :=
  rfl

/-- The vanishing functor includes in the ambient space by forgetting the vanishing law. -/
def subschemeFunctorι (I : IdealSubobject X) : subschemeFunctor I ⟶ X.functorOfPoints where
  app T := TypeCat.ofHom Subtype.val
  naturality := by intros; rfl

/-- The vanishing-functor inclusion is pointwise injective. -/
instance subschemeFunctorι_mono (I : IdealSubobject X) : Mono (subschemeFunctorι I) := by
  have : ∀ T, Mono ((subschemeFunctorι I).app T) :=
    fun T ↦ ConcreteCategory.mono_of_injective _ Subtype.val_injective
  exact NatTrans.mono_of_mono_app _

/-- The diagonal of the vanishing functor uses the supplied ambient diagonal pullbacks. -/
theorem subschemeFunctor_representableDiagonal (I : IdealSubobject X) :
    yoneda.relativelyRepresentable (Limits.diag (subschemeFunctor I)) :=
  @Functor.relativelyRepresentable.diagonal_of_mono
    _ _ ((Over S)ᵒᵖ ⥤ Type u) _ yoneda _ _ _ _
    (subschemeFunctorι I) (subschemeFunctorι_mono I)
    X.representableDiagonal

namespace SubschemeAtlas

/-- An affine open of the original scheme atlas, over the original base. -/
def affineOver (X : AlgebraicSpace S) (U : (AtlasInput.scheme X).left.affineOpens) :
    Over S :=
  Over.mk (U.1.ι ≫ (AtlasInput.scheme X).hom)

/-- The affine open maps to `X` through the atlas supplied by the input. -/
def affineMap (X : AlgebraicSpace S) (U : (AtlasInput.scheme X).left.affineOpens) :
    ofOver (affineOver X U) ⟶ X :=
  yoneda.map (Over.homMk U.1.ι rfl : affineOver X U ⟶ AtlasInput.scheme X) ≫
    AtlasInput.map X

/-- Open restrictions of the supplied étale atlas remain étale over `X`. -/
theorem affineMap_etale (X : AlgebraicSpace S)
    (U : (AtlasInput.scheme X).left.affineOpens) : Etale (affineMap X U) := sorry

/-- The actual affine open, as an object on which the input ideal sheaf is evaluated. -/
def chart (X : AlgebraicSpace S) (U : (AtlasInput.scheme X).left.affineOpens) :
    smallEtaleSite X :=
  smallEtaleSite.mk (affineMap X U) (affineMap_etale X U)

/-- The image ideal on an affine open of the input atlas, transported by the native
comparison from global sections of the open subscheme to sections on the open. -/
def sectionIdeal (I : IdealSubobject X) (U : (AtlasInput.scheme X).left.affineOpens) :
    Ideal Γ((AtlasInput.scheme X).left, U.1) :=
  Ideal.map U.1.topIso.hom.hom
    (LinearMap.range (I.arrow.val.app (op (chart X U))).hom)

/-- The native ideal-sheaf datum attached to the affine-open image ideals. -/
def idealSheafData (I : IdealSubobject X) : (AtlasInput.scheme X).left.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals (sectionIdeal I)

/-- Quasi-coherence makes the affine-open image ideals a compatible ideal sheaf. -/
theorem idealSheafData_ideal (I : IdealSubobject X) [IsQuasiCoherent I]
    (U : (AtlasInput.scheme X).left.affineOpens) :
    (idealSheafData I).ideal U = sectionIdeal I U := sorry

/-- The native closed scheme cut out on the original atlas, over the original base. -/
def over (I : IdealSubobject X) : Over S :=
  Over.mk ((idealSheafData I).subschemeι ≫ (AtlasInput.scheme X).hom)

/-- The underlying map retains the native closed-scheme inclusion and original atlas map. -/
def ambientMap (I : IdealSubobject X) : yoneda.obj (over I) ⟶ X.functorOfPoints :=
  yoneda.map (Over.homMk (idealSheafData I).subschemeι rfl :
    over I ⟶ AtlasInput.scheme X) ≫ AtlasInput.map X

/-- Every point of the closed scheme on the input atlas annihilates the original ideal. -/
theorem ambientMap_vanishes (I : IdealSubobject X) [IsQuasiCoherent I]
    (T : (Over S)ᵒᵖ) (h : (yoneda.obj (over I)).obj T) :
    vanishes (homOfPoint ((ambientMap I).app T h)) I := sorry

/-- The actual atlas map into the vanishing subfunctor retains every ambient point. -/
def map (I : IdealSubobject X) [IsQuasiCoherent I] :
    yoneda.obj (over I) ⟶ subschemeFunctor I where
  app T := TypeCat.ofHom fun h ↦
    ⟨(ambientMap I).app T h, ambientMap_vanishes I T h⟩
  naturality := sorry

/-- On scheme-valued points, the atlas map is the ambient map with its vanishing law. -/
theorem map_app (I : IdealSubobject X) [IsQuasiCoherent I]
    (T : (Over S)ᵒᵖ) (h : (yoneda.obj (over I)).obj T) :
    ((map I).app T h).val = (ambientMap I).app T h := rfl

/-- The specified closed scheme on the original atlas is étale over the vanishing functor. -/
theorem map_etale (I : IdealSubobject X) [IsQuasiCoherent I] :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (map I) := sorry

/-- The specified closed scheme on the original atlas covers the vanishing functor. -/
theorem map_locallySurjective (I : IdealSubobject X) [IsQuasiCoherent I] :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (map I) := sorry

end SubschemeAtlas

/-- The closed subspace of `X` cut out by a quasi-coherent ideal sheaf. -/
def subscheme (I : IdealSubobject X) [IsQuasiCoherent I] : AlgebraicSpace S :=
  ofFunctor (subschemeFunctor I) sorry (subschemeFunctor_representableDiagonal I)
    ⟨SubschemeAtlas.over I, SubschemeAtlas.map I,
      SubschemeAtlas.map_etale I, SubschemeAtlas.map_locallySurjective I⟩

/-- The functor of points of `subscheme I` is `subschemeFunctor I`. -/
@[simp]
theorem subscheme_functorOfPoints (I : IdealSubobject X) [IsQuasiCoherent I] :
    (subscheme I).functorOfPoints = subschemeFunctor I :=
  rfl

/-- The closed-subspace inclusion of the locus cut out by `I` into `X`. -/
def subschemeι (I : IdealSubobject X) [IsQuasiCoherent I] : subscheme I ⟶ X :=
  subschemeFunctorι I

/-- On `T`-points, `subschemeι I` forgets the vanishing witness. -/
theorem subschemeι_app (I : IdealSubobject X) [IsQuasiCoherent I]
    (T : (Over S)ᵒᵖ) (h : (subschemeFunctor I).obj T) :
    (subschemeι I).app T h = h.val :=
  sorry

/-- The inclusion of the closed subspace cut out by `I` is a closed immersion. -/
instance instIsClosedImmersion_subschemeι (I : IdealSubobject X)
    [IsQuasiCoherent I] : IsClosedImmersion (subschemeι I) :=
  sorry

/-- The closed subspace cut out by `I` has functor of points `subschemeFunctor I`,
and its inclusion into `X` is a closed immersion. -/
theorem subscheme_spec (I : IdealSubobject X) [IsQuasiCoherent I] :
    (subscheme I).functorOfPoints = subschemeFunctor I ∧
      IsClosedImmersion (subschemeι I) :=
  sorry

/-- The scheme-theoretic intersection of the closed subspaces cut out by
quasi-coherent ideals `I` and `J` is the closed subspace cut out by `I ⊔ J`. -/
noncomputable abbrev schemeTheoreticIntersection (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] : AlgebraicSpace S :=
  subscheme (I ⊔ J)

/-- Scheme-theoretic intersection is the closed subspace attached to the sum of
ideal sheaves. -/
@[simp]
theorem schemeTheoreticIntersection_eq_subscheme_sup (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticIntersection I J = subscheme (I ⊔ J) :=
  rfl

/-- The closed-subspace inclusion of a scheme-theoretic intersection. -/
noncomputable abbrev schemeTheoreticIntersectionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticIntersection I J ⟶ X :=
  subschemeι (I ⊔ J)

/-- The inclusion of a scheme-theoretic intersection is a closed immersion. -/
instance instIsClosedImmersion_schemeTheoreticIntersectionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsClosedImmersion (schemeTheoreticIntersectionι I J) :=
  instIsClosedImmersion_subschemeι (I ⊔ J)

/-- Scheme-theoretic intersection is cut out by `I ⊔ J` and includes as a closed
immersion. -/
theorem schemeTheoreticIntersection_spec (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticIntersection I J = subscheme (I ⊔ J) ∧
      IsClosedImmersion (schemeTheoreticIntersectionι I J) :=
  sorry

/-- The scheme-theoretic union of the closed subspaces cut out by quasi-coherent
ideals `I` and `J` is the closed subspace cut out by `I ⊓ J`. -/
noncomputable abbrev schemeTheoreticUnion (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] : AlgebraicSpace S :=
  subscheme (I ⊓ J)

/-- Scheme-theoretic union is the closed subspace attached to the intersection of
ideal sheaves. -/
@[simp]
theorem schemeTheoreticUnion_eq_subscheme_inf (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnion I J = subscheme (I ⊓ J) :=
  rfl

/-- The closed-subspace inclusion of a scheme-theoretic union. -/
noncomputable abbrev schemeTheoreticUnionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnion I J ⟶ X :=
  subschemeι (I ⊓ J)

/-- The inclusion of a scheme-theoretic union is a closed immersion. -/
instance instIsClosedImmersion_schemeTheoreticUnionι (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    IsClosedImmersion (schemeTheoreticUnionι I J) :=
  instIsClosedImmersion_subschemeι (I ⊓ J)

/-- Scheme-theoretic union is cut out by `I ⊓ J` and includes as a closed
immersion. -/
theorem schemeTheoreticUnion_spec (I J : IdealSubobject X)
    [IsQuasiCoherent I] [IsQuasiCoherent J] :
    schemeTheoreticUnion I J = subscheme (I ⊓ J) ∧
      IsClosedImmersion (schemeTheoreticUnionι I J) :=
  sorry

namespace ClosedSubspace

/-- The kernel of `𝒪_X ⟶ ι_* 𝒪_Z`, as an ideal subobject of `𝒪_X`. -/
noncomputable abbrev idealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) : IdealSubobject X :=
  Hom.idealSheafSubobject Z.ι

/-- The ideal sheaf of a closed subspace is the kernel subobject of its inclusion. -/
theorem idealSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) :
    Z.idealSheaf = Hom.idealSheafSubobject Z.ι :=
  sorry

/-- The closed subspace of `X` cut out by a quasi-coherent ideal sheaf. -/
noncomputable def ofQuasiCoherentIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] : ClosedSubspace X where
  X := subscheme I
  ι := subschemeι I
  isClosedImmersion := instIsClosedImmersion_subschemeι I

end ClosedSubspace

/-- For a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the sheaf `i_* 𝒪_Z` is a quasi-coherent `𝒪_X`-module. -/
instance IsClosedImmersion.pushforwardUnit_isQuasicoherent {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    ((Modules.pushforward i).obj (SheafOfModules.unit (structureSheaf Z))).IsQuasicoherent :=
  sorry

/-- The inclusion of the closed subspace cut out by `I` is `subschemeι I`. -/
theorem ClosedSubspace.ofQuasiCoherentIdeal_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (ClosedSubspace.ofQuasiCoherentIdeal I).ι = subschemeι I :=
  sorry

namespace Hom

/-- For a closed immersion `i : Z ⟶ X` of algebraic spaces over a
scheme `S`, the map `i^♯ : 𝒪_X ⟶ i_* 𝒪_Z` is surjective as an `𝒪_X`-module map. -/
instance idealSheafMap_epi {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] : Epi (idealSheafMap i) :=
  sorry

/-- Every quasi-coherent sheaf of ideals on `X` arises as the
kernel ideal sheaf of the closed subspace it cuts out. -/
theorem _root_.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) [IsQuasiCoherent I] :
    (ClosedSubspace.ofQuasiCoherentIdeal I).idealSheaf = I :=
  sorry

end Hom

namespace ClosedSubspace

/-- Closed subspaces of `X` are determined up to isomorphism over
`X` by their kernel ideal sheaves. -/
theorem overIso_iff_idealSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z W : ClosedSubspace X) :
    Nonempty (Over.mk Z.ι ≅ Over.mk W.ι) ↔ Z.idealSheaf = W.idealSheaf :=
  sorry

/-- The rule sending a closed subspace to its kernel ideal sheaf
is inclusion-reversing. -/
theorem idealSheaf_le_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z W : ClosedSubspace X) :
    W.idealSheaf ≤ Z.idealSheaf ↔ ∃ f : Z.X ⟶ W.X, f ≫ W.ι = Z.ι :=
  sorry

end ClosedSubspace

/-- A morphism `h : Y ⟶ X` of algebraic spaces factors through a
closed immersion `i : Z ⟶ X` if and only if `h^* I ⟶ 𝒪_Y` is zero, where `I` is
the kernel of `𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem IsClosedImmersion.exists_lift_iff_vanishes {S : Scheme.{u}}
    {Y Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (h : Y ⟶ X) :
    (∃ φ : Y ⟶ Z, φ ≫ i = h) ↔ vanishes h (Hom.idealSheafSubobject i) :=
  sorry

/-- A closed immersion is a monomorphism, so a factorization through `Z` is unique
when it exists. -/
theorem IsClosedImmersion.existsUnique_lift_iff_vanishes {S : Scheme.{u}}
    {Y Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (h : Y ⟶ X) :
    (∃! φ : Y ⟶ Z, φ ≫ i = h) ↔ vanishes h (Hom.idealSheafSubobject i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
