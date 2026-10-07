module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap94.Lemma_94_19_1_Localization

/-!
# Separation axioms for algebraic stacks

An algebraic stack over `S` is DM, quasi-DM, separated, or quasi-separated over
`S` when its structure morphism is. Absolute versions are the same properties
after viewing the stack over `Spec ℤ` by Construction A.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

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
  sorry

/-- Unramifiedness of the object diagonal witnesses that an algebraic stack is
DM over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : Groupoids.Hom.has (@AlgebraicSpace.Unramified S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsDMOver X :=
  sorry

/-- An algebraic stack is DM over `S` if and only if its structure morphism is
DM. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsDMOver X ↔ DM (baseProjection.{u + 1, u, u + 1} X) :=
  sorry

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
  sorry

/-- Local quasi-finiteness of the object diagonal witnesses that an algebraic
stack is quasi-DM over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : Groupoids.Hom.has (@AlgebraicSpace.LocallyQuasiFinite S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsQuasiDMOver X :=
  sorry

/-- An algebraic stack is quasi-DM over `S` if and only if its structure
morphism is quasi-DM. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsQuasiDMOver X ↔ QuasiDM (baseProjection.{u + 1, u, u + 1} X) :=
  sorry

end IsQuasiDMOver

/-- The canonical slice of a scheme over `S` is quasi-DM over `S`. -/
instance instIsQuasiDMOver_slice {S : Scheme.{u}} (U : Over S) :
    IsQuasiDMOver (GroupoidsOver.slice U) :=
  sorry

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
  sorry

/-- Properness of the object diagonal witnesses that an algebraic stack is
separated over `S`. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : Groupoids.Hom.has (@AlgebraicSpace.Proper S)
      (diagonal.{u + 1, u, u + 1} X)) :
    IsSeparatedOver X :=
  sorry

/-- An algebraic stack is separated over `S` if and only if its structure
morphism is separated. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsSeparatedOver X ↔ Separated (baseProjection.{u + 1, u, u + 1} X) :=
  sorry

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
  sorry

/-- The object diagonal of an algebraic stack that is quasi-separated over `S`
is quasi-compact and quasi-separated. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiSeparatedOver X] :
    Groupoids.Hom.has (@AlgebraicSpace.QuasiCompact S)
        (diagonal.{u + 1, u, u + 1} X) ∧
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (diagonal.{u + 1, u, u + 1} X) :=
  sorry

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
  sorry

/-- An algebraic stack is quasi-separated over `S` if and only if its structure
morphism is quasi-separated. -/
theorem iff_baseProjection {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))] :
    IsQuasiSeparatedOver X ↔
      QuasiSeparated (baseProjection.{u + 1, u, u + 1} X) :=
  sorry

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
  /-- The stack is DM over `Spec ℤ` after Construction A. -/
  overSpecZ : IsDMOver (viewedOver (specULiftZIsTerminal.from S) X)

namespace IsDM

/-- An algebraic stack that is DM is DM over `Spec ℤ` after Construction A. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsDM X] :
    IsDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  sorry

/-- Being DM over `Spec ℤ` after Construction A witnesses that an algebraic
stack is DM. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsDMOver (viewedOver (specULiftZIsTerminal.from S) X)) :
    IsDM X :=
  sorry

/-- An algebraic stack is DM if and only if it is DM over `Spec ℤ` after
Construction A. -/
theorem iff_overSpecZ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsDM X ↔ IsDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  sorry

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
  /-- The stack is quasi-DM over `Spec ℤ` after Construction A. -/
  overSpecZ : IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X)

namespace IsQuasiDM

/-- An algebraic stack that is quasi-DM is quasi-DM over `Spec ℤ` after
Construction A. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsQuasiDM X] :
    IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  sorry

/-- Being quasi-DM over `Spec ℤ` after Construction A witnesses that an
algebraic stack is quasi-DM. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X)) :
    IsQuasiDM X :=
  sorry

/-- An algebraic stack is quasi-DM if and only if it is quasi-DM over `Spec ℤ`
after Construction A. -/
theorem iff_overSpecZ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsQuasiDM X ↔ IsQuasiDMOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  sorry

end IsQuasiDM

/-- The canonical slice of a scheme over `S` is a quasi-DM algebraic stack. -/
instance instIsQuasiDM_slice {S : Scheme.{u}} (U : Over S) :
    IsQuasiDM (GroupoidsOver.slice U) :=
  sorry

/-- An algebraic stack is separated if, after viewing over `Spec ℤ`, it is
separated over `Spec ℤ`. -/
@[mk_iff]
class IsSeparated {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Prop where
  /-- The stack is separated over `Spec ℤ` after Construction A. -/
  overSpecZ : IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X)

namespace IsSeparated

/-- An algebraic stack that is separated is separated over `Spec ℤ` after
Construction A. -/
theorem spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    [IsSeparated X] :
    IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  sorry

/-- Being separated over `Spec ℤ` after Construction A witnesses that an
algebraic stack is separated. -/
theorem of {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (h : IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X)) :
    IsSeparated X :=
  sorry

/-- An algebraic stack is separated if and only if it is separated over
`Spec ℤ` after Construction A. -/
theorem iff_overSpecZ {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    IsSeparated X ↔
      IsSeparatedOver (viewedOver (specULiftZIsTerminal.from S) X) :=
  sorry

end IsSeparated

/-- The canonical slice of a separated scheme is a separated algebraic stack. -/
instance instIsSeparated_slice {S : Scheme.{u}} (U : Over S)
    [U.left.IsSeparated] :
    IsSeparated (GroupoidsOver.slice U) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
