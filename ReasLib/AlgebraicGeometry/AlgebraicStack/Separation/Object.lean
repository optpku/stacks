/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ChangeOfBase
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Separation axioms for algebraic stacks

An algebraic stack over `S` is DM, quasi-DM, separated, or quasi-separated over
`S` when its structure morphism is. Absolute versions are the same properties
after viewing the stack over `Spec ℤ` by postcomposing the projection along the canonical map to `Spec ℤ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

private theorem has_locallyQuasiFinite_of_unramified {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {f : X ⟶ Y}
    (hf : Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f) :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S) f := by
  intro U y Fy fy hfy
  refine ⟨?_⟩
  intro V W a b h ha hb w
  have hu := (hf y Fy fy hfy).of_etale a b h ha hb w
  letI := hu.toFormallyUnramified
  letI := hu.toLocallyOfFiniteType
  refine ⟨?_⟩
  intro V' hV' W' hW' e
  have hft := h.left.finiteType_appLE hV' hW' e
  have hfu := h.left.formallyUnramified_appLE hV' hW' e
  algebraize [(h.left.appLE V' W' e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- An algebraic stack over `S` is DM over `S` if its object diagonal is
unramified as a morphism representable by algebraic spaces. -/
@[mk_iff]
class IsDMOver {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- The object diagonal is unramified. -/
  unramified_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (diagonal.{u + 1, u, u + 1} X)

namespace IsDMOver

/-- The object diagonal of an algebraic stack that is DM over `S` is
unramified. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDMOver X] :
    Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (diagonal.{u + 1, u, u + 1} X) :=
  IsDMOver.unramified_diagonal

/-- Unramifiedness of the object diagonal witnesses that an algebraic stack is
DM over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsDMOver X :=
  ⟨h⟩

/-- An algebraic stack is DM over `S` if and only if its structure morphism is
DM. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsDMOver X ↔ DM (baseProjection.{u + 1, u, u + 1} X) :=
  ⟨fun h => ⟨h.unramified_diagonal⟩, fun h => ⟨h.unramified_diagonal⟩⟩

end IsDMOver

/-- The canonical slice of a scheme over `S` is DM over `S`. -/
instance instIsDMOver_slice {S : Scheme.{u}} (U : Over S) :
    IsDMOver (GroupoidsOver.slice U) :=
  sorry

/-- An algebraic stack over `S` is quasi-DM over `S` if its object diagonal is
locally quasi-finite as a morphism representable by algebraic spaces. -/
@[mk_iff]
class IsQuasiDMOver {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- The object diagonal is locally quasi-finite. -/
  locallyQuasiFinite_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (diagonal.{u + 1, u, u + 1} X)

namespace IsQuasiDMOver

/-- The object diagonal of an algebraic stack that is quasi-DM over `S` is
locally quasi-finite. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiDMOver X] :
    Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (diagonal.{u + 1, u, u + 1} X) :=
  IsQuasiDMOver.locallyQuasiFinite_diagonal

/-- Local quasi-finiteness of the object diagonal witnesses that an algebraic
stack is quasi-DM over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsQuasiDMOver X :=
  ⟨h⟩

/-- An algebraic stack is quasi-DM over `S` if and only if its structure
morphism is quasi-DM. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsQuasiDMOver X ↔ QuasiDM (baseProjection.{u + 1, u, u + 1} X) :=
  ⟨fun h => ⟨h.locallyQuasiFinite_diagonal⟩,
    fun h => ⟨h.locallyQuasiFinite_diagonal⟩⟩

end IsQuasiDMOver

/-- The canonical slice of a scheme over `S` is quasi-DM over `S`. -/
instance instIsQuasiDMOver_slice {S : Scheme.{u}} (U : Over S) :
    IsQuasiDMOver (GroupoidsOver.slice U) :=
  ⟨has_locallyQuasiFinite_of_unramified (IsDMOver.spec _)⟩

/-- An algebraic stack over `S` is separated over `S` if its object diagonal is
proper as a morphism representable by algebraic spaces. -/
@[mk_iff]
class IsSeparatedOver {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- The object diagonal is proper. -/
  proper_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (diagonal.{u + 1, u, u + 1} X)

namespace IsSeparatedOver

/-- The object diagonal of an algebraic stack that is separated over `S` is
proper. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsSeparatedOver X] :
    Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (diagonal.{u + 1, u, u + 1} X) :=
  IsSeparatedOver.proper_diagonal

/-- Properness of the object diagonal witnesses that an algebraic stack is
separated over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsSeparatedOver X :=
  ⟨h⟩

/-- An algebraic stack is separated over `S` if and only if its structure
morphism is separated. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsSeparatedOver X ↔ Separated (baseProjection.{u + 1, u, u + 1} X) :=
  ⟨fun h => ⟨h.proper_diagonal⟩, fun h => ⟨h.proper_diagonal⟩⟩

end IsSeparatedOver

/-- The canonical slice of a scheme separated over `S` is separated over `S`. -/
instance instIsSeparatedOver_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsSeparated U.hom] :
    IsSeparatedOver (GroupoidsOver.slice U) :=
  sorry

/-- An algebraic stack over `S` is quasi-separated over `S` if its object
diagonal is quasi-compact and quasi-separated as a morphism representable by
algebraic spaces. -/
@[mk_iff]
class IsQuasiSeparatedOver {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] : Prop where
  /-- The object diagonal is quasi-compact. -/
  quasiCompact_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
      (diagonal.{u + 1, u, u + 1} X)
  /-- The object diagonal is quasi-separated. -/
  quasiSeparated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
      (diagonal.{u + 1, u, u + 1} X)

namespace IsQuasiSeparatedOver

/-- An algebraic stack is quasi-separated over `S` if and only if its object
diagonal is quasi-compact and quasi-separated. -/
theorem iff {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsQuasiSeparatedOver X ↔
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
          (diagonal.{u + 1, u, u + 1} X) ∧
        Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
          (diagonal.{u + 1, u, u + 1} X) :=
  ⟨fun h => ⟨h.quasiCompact_diagonal, h.quasiSeparated_diagonal⟩,
    fun h => ⟨h.1, h.2⟩⟩

/-- The object diagonal of an algebraic stack that is quasi-separated over `S`
is quasi-compact and quasi-separated. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiSeparatedOver X] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (diagonal.{u + 1, u, u + 1} X) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (diagonal.{u + 1, u, u + 1} X) :=
  ⟨IsQuasiSeparatedOver.quasiCompact_diagonal,
    IsQuasiSeparatedOver.quasiSeparated_diagonal⟩

/-- Quasi-compactness and quasi-separatedness of the object diagonal witness
that an algebraic stack is quasi-separated over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h_quasiCompact :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (diagonal.{u + 1, u, u + 1} X))
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (diagonal.{u + 1, u, u + 1} X)) :
    IsQuasiSeparatedOver X :=
  ⟨h_quasiCompact, h_quasiSeparated⟩

/-- An algebraic stack is quasi-separated over `S` if and only if its structure
morphism is quasi-separated. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsQuasiSeparatedOver X ↔
      QuasiSeparated (baseProjection.{u + 1, u, u + 1} X) :=
  ⟨fun h => ⟨h.quasiCompact_diagonal, h.quasiSeparated_diagonal⟩,
    fun h => ⟨h.quasiCompact_diagonal, h.quasiSeparated_diagonal⟩⟩

end IsQuasiSeparatedOver

/-- The canonical slice of a scheme quasi-separated over `S` is quasi-separated
over `S`. -/
instance instIsQuasiSeparatedOver_slice {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.QuasiSeparated U.hom] :
    IsQuasiSeparatedOver (GroupoidsOver.slice U) :=
  sorry

/-- An algebraic stack is DM if, after viewing over `Spec ℤ`, it is DM over
`Spec ℤ`. -/
@[mk_iff]
class IsDM {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] : Prop where
  /-- The stack is DM over `Spec ℤ` after viewing along the canonical map to `Spec ℤ`. -/
  overSpecZ : IsDMOver (viewedOver (specULiftZIsTerminal.from S) X)

namespace IsDM

/-- An algebraic stack that is DM is DM over `Spec ℤ` after viewing along the canonical map to `Spec ℤ`. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDM X] :
    IsDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  IsDM.overSpecZ

/-- Being DM over `Spec ℤ` after viewing along the canonical map to `Spec ℤ` witnesses that an algebraic
stack is DM. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsDMOver (viewedOver (specULiftZIsTerminal.from S) X)) :
    IsDM X :=
  ⟨h⟩

/-- An algebraic stack is DM if and only if it is DM over `Spec ℤ` after
Construction A. -/
theorem iff_overSpecZ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsDM X ↔ IsDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  ⟨fun h => h.overSpecZ, fun h => ⟨h⟩⟩

end IsDM

/-- The canonical slice of a scheme over `S` is a DM algebraic stack. -/
instance instIsDM_slice {S : Scheme.{u}} (U : Over S) :
    IsDM (GroupoidsOver.slice U) :=
  sorry

/-- An algebraic stack is quasi-DM if, after viewing over `Spec ℤ`, it is
quasi-DM over `Spec ℤ`. -/
@[mk_iff]
class IsQuasiDM {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- The stack is quasi-DM over `Spec ℤ` after viewing along the canonical map to `Spec ℤ`. -/
  overSpecZ : IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X)

namespace IsQuasiDM

/-- An algebraic stack that is quasi-DM is quasi-DM over `Spec ℤ` after
Construction A. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiDM X] :
    IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  IsQuasiDM.overSpecZ

/-- Being quasi-DM over `Spec ℤ` after viewing along the canonical map to `Spec ℤ` witnesses that an
algebraic stack is quasi-DM. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X)) :
    IsQuasiDM X :=
  ⟨h⟩

/-- An algebraic stack is quasi-DM if and only if it is quasi-DM over `Spec ℤ`
after viewing along the canonical map to `Spec ℤ`. -/
theorem iff_overSpecZ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsQuasiDM X ↔ IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  ⟨fun h => h.overSpecZ, fun h => ⟨h⟩⟩

end IsQuasiDM

/-- The canonical slice of a scheme over `S` is a quasi-DM algebraic stack. -/
instance instIsQuasiDM_slice {S : Scheme.{u}} (U : Over S) :
    IsQuasiDM (GroupoidsOver.slice U) :=
  ⟨⟨has_locallyQuasiFinite_of_unramified
    (IsDM.spec (GroupoidsOver.slice U)).unramified_diagonal⟩⟩

/-- An algebraic stack is separated if, after viewing over `Spec ℤ`, it is
separated over `Spec ℤ`. -/
@[mk_iff]
class IsSeparated {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- The stack is separated over `Spec ℤ` after viewing along the canonical map to `Spec ℤ`. -/
  overSpecZ : IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X)

namespace IsSeparated

/-- An algebraic stack that is separated is separated over `Spec ℤ` after
Construction A. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsSeparated X] :
    IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  IsSeparated.overSpecZ

/-- Being separated over `Spec ℤ` after viewing along the canonical map to `Spec ℤ` witnesses that an
algebraic stack is separated. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X)) :
    IsSeparated X :=
  ⟨h⟩

/-- An algebraic stack is separated if and only if it is separated over
`Spec ℤ` after viewing along the canonical map to `Spec ℤ`. -/
theorem iff_overSpecZ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsSeparated X ↔
      IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  ⟨fun h => h.overSpecZ, fun h => ⟨h⟩⟩

end IsSeparated

/-- The canonical slice of a separated scheme is a separated algebraic stack. -/
instance instIsSeparated_slice {S : Scheme.{u}} (U : Over S)
    [U.left.IsSeparated] :
    IsSeparated (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
