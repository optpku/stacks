/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Closure
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Category

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- The category of compactifications of the fixed scheme `X` over `S`. -/
abbrev Of (S : Scheme.{u}) (X : Over S) :=
  ObjectProperty.FullSubcategory
    (fun j : Under X ↦ Compactification.Is S (Arrow.mk j.hom))

namespace Of

/-- A fixed-interior compactification carries the general compactification property. -/
instance instIs (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    Compactification.Is S (Arrow.mk P.obj.hom) := P.property

/-- The interior map of a fixed-interior compactification is quasi-compact. -/
instance instQuasiCompact (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    QuasiCompact P.obj.hom.left := P.property.quasiCompact

/-- The ambient scheme of a fixed-interior compactification is proper over the base. -/
instance instIsProper (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsProper P.obj.right.hom := P.property.isProper

/-- Construct a fixed-interior compactification from its ambient scheme and interior map. -/
def mk (S : Scheme.{u}) {X : Over S} (Xbar : Over S) (j : X ⟶ Xbar)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper Xbar.hom] : Of S X :=
  ⟨Under.mk j,
    { isOpenImmersion := inferInstanceAs (IsOpenImmersion j.left)
      quasiCompact := inferInstanceAs (QuasiCompact j.left)
      isProper := inferInstanceAs (IsProper Xbar.hom) }⟩

/-- The interior immersion of a fixed-interior compactification. -/
def ι {S : Scheme.{u}} {X : Over S} (P : Of S X) : X.left ⟶ P.obj.right.left :=
  P.obj.hom.left

/-- The interior immersion of a fixed-interior compactification is an open immersion. -/
instance instIsOpenImmersion (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsOpenImmersion (ι P) := P.property.isOpenImmersion

/-- The constructed compactification has the specified interior immersion. -/
theorem mk_ι (S : Scheme.{u}) {X : Over S} (Xbar : Over S) (j : X ⟶ Xbar)
    [IsOpenImmersion j.left] [QuasiCompact j.left] [IsProper Xbar.hom] :
    ι (mk S Xbar j) = j.left := sorry

/-- Regard a fixed-interior compactification as a general compactification over `S`. -/
def toCompactification {S : Scheme.{u}} {X : Over S} (P : Of S X) :
    Compactification S :=
  ⟨Arrow.mk P.obj.hom, P.property⟩

/-- The general compactification underlying `P` has the expected arrow. -/
theorem toCompactification_obj {S : Scheme.{u}} {X : Over S} (P : Of S X) :
    (toCompactification P).obj = Arrow.mk P.obj.hom := sorry

/-- The map of ambient schemes underlying a morphism of fixed-interior compactifications. -/
def ambientMap {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (f : P ⟶ Q) :
    P.obj.right.left ⟶ Q.obj.right.left :=
  f.hom.right.left

/-- A morphism of fixed-interior compactifications commutes with the interior immersions. -/
theorem ι_comp_ambientMap {S : Scheme.{u}} {X : Over S} {P Q : Of S X} (f : P ⟶ Q) :
    ι P ≫ ambientMap f = ι Q := sorry

end Of

/-- A fixed-interior compactification is dense when its interior is both topologically and
scheme-theoretically dense in its ambient scheme. -/
class IsDense (S : Scheme.{u}) (X : Over S) (P : Of S X) : Prop where
  /-- The interior immersion has dense image. -/
  isDominant : IsDominant (Of.ι P)
  /-- The open image of the interior is scheme-theoretically dense. -/
  schemeTheoreticallyDense : schemeTheoreticallyDense (Of.ι P).opensRange

namespace IsDense

/-- Density of a fixed-interior compactification exposes its topological and
scheme-theoretic conditions together. -/
theorem isDense_iff (S : Scheme.{u}) (X : Over S) (P : Of S X) :
    IsDense S X P ↔
      DenseRange (Of.ι P) ∧
        AlgebraicGeometry.schemeTheoreticallyDense (Of.ι P).opensRange := sorry

/-- A dense fixed-interior compactification has a dominant interior immersion. -/
instance instIsDominant (S : Scheme.{u}) (X : Over S) (P : Of S X)
    [h : IsDense S X P] : IsDominant (Of.ι P) := h.isDominant

end IsDense

/-- The full subcategory of compactifications whose fixed interior is topologically and
scheme-theoretically dense. -/
abbrev DenseOf (S : Scheme.{u}) (X : Over S) :=
  ObjectProperty.FullSubcategory (IsDense S X)

namespace DenseOf

/-- A bundled dense compactification carries its defining density property. -/
instance instIsDense (S : Scheme.{u}) (X : Over S) (P : DenseOf S X) :
    IsDense S X P.obj := P.property

/-- The inclusion of dense fixed-interior compactifications into all compactifications. -/
def inclusion (S : Scheme.{u}) (X : Over S) : DenseOf S X ⥤ Of S X :=
  ObjectProperty.ι (IsDense S X)

/-- The dense-compactification inclusion forgets only the density property. -/
theorem inclusion_obj (S : Scheme.{u}) (X : Over S) (P : DenseOf S X) :
    (inclusion S X).obj P = P.obj := sorry

end DenseOf

namespace Of

/-- Over a quasi-compact quasi-separated base, fixed-interior compactifications of a
compactifiable scheme form a cofiltered category. -/
instance instIsCofiltered (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (X : Over S) [Nonempty (Of S X)] : IsCofiltered (Of S X) := sorry

end Of

namespace DenseOf

/-- Compactifications with topologically and scheme-theoretically dense fixed interior form
an initial full subcategory of all fixed-interior compactifications. -/
instance instInitialInclusion (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] (X : Over S) [Nonempty (Of S X)] :
    Functor.Initial (inclusion S X) := sorry

end DenseOf

namespace Of

/-- A morphism of fixed-interior compactifications with dense source interior pulls the open
image of the target interior back to the open image of the source interior. -/
theorem preimage_opensRange (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (X : Over S) [Nonempty (Of S X)] {P' P : Of S X} (f : P' ⟶ P)
    [IsDominant (ι P')] :
    ambientMap f ⁻¹ᵁ (ι P).opensRange = (ι P').opensRange := sorry

end Of

end AlgebraicGeometry.Scheme.Compactification
