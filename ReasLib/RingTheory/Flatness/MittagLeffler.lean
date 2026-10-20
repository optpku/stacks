module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.HomInverseSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

noncomputable section

namespace Module

section

variable {R : Type u} [Ring R]
variable {I : Type v} [Preorder I]

/-- A directed system of `R`-modules is Mittag-Leffler if each stage is finitely presented
and its Hom inverse system is Mittag-Leffler for every `R`-module. -/
@[stacks 059A]
def IsMittagLefflerDirectedSystem [Nonempty I] [IsDirectedOrder I]
    (M : I ⥤ ModuleCat.{w} R) : Prop :=
  (∀ i, Module.FinitePresentation R (M.obj i)) ∧ M.HomMittagLeffler

namespace IsMittagLefflerDirectedSystem

/-- Every stage of a Mittag-Leffler directed system is finitely presented. -/
@[stacks 059A "finite-presentation stages"]
theorem finitePresentation [Nonempty I] [IsDirectedOrder I]
    {F : I ⥤ ModuleCat.{w} R} (hF : IsMittagLefflerDirectedSystem F) (i : I) :
    Module.FinitePresentation R (F.obj i) := hF.1 i

/-- Every Hom inverse system associated to a Mittag-Leffler directed system is
Mittag-Leffler. -/
@[stacks 059A "Hom criterion"]
theorem homMittagLeffler [Nonempty I] [IsDirectedOrder I]
    {F : I ⥤ ModuleCat.{w} R} (hF : IsMittagLefflerDirectedSystem F) :
    F.HomMittagLeffler := hF.2

end IsMittagLefflerDirectedSystem

end

section

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace MittagLeffler

/-- A concrete directed colimit presentation of an `R`-module by a
Mittag-Leffler directed system. -/
@[stacks 059F "presentation"]
structure Presentation (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] where
  /-- The directed index type. -/
  index : Type w
  /-- The preorder on the index type. -/
  [indexPreorder : Preorder index]
  /-- The index type is nonempty. -/
  [indexNonempty : Nonempty index]
  /-- The index preorder is directed. -/
  [indexDirected : IsDirectedOrder index]
  /-- The concrete colimit presentation of the universe lift of the module.  Its carrier universe
  contains the ring, the original module, and the index type, so finite-presentation compactness
  applies without a hidden universe restriction. -/
  toColimitPresentation :
    ColimitPresentation index
      (ModuleCat.of.{max u v w} R (ULift.{max u w} M))
  /-- The presentation diagram is a Mittag-Leffler directed system. -/
  isMittagLeffler : IsMittagLefflerDirectedSystem toColimitPresentation.diag

/-- The diagram underlying a Mittag-Leffler presentation. -/
abbrev Presentation.diag (P : Presentation.{u, v, w} R M) :=
  @ColimitPresentation.diag _ _ P.index
    (@Preorder.smallCategory P.index P.indexPreorder) _ P.toColimitPresentation

/-- The structure maps from the stages of a Mittag-Leffler presentation to the presented
module. -/
abbrev Presentation.ι (P : Presentation.{u, v, w} R M) :=
  @ColimitPresentation.ι _ _ P.index
    (@Preorder.smallCategory P.index P.indexPreorder) _ P.toColimitPresentation

/-- Build a Mittag-Leffler presentation from a concrete directed colimit presentation and the
Mittag-Leffler property of its diagram. -/
def Presentation.ofColimit
    {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (P : ColimitPresentation I
      (ModuleCat.of.{max u v w} R (ULift.{max u w} M)))
    (hP : IsMittagLefflerDirectedSystem P.diag) : Presentation.{u, v, w} R M where
  index := I
  toColimitPresentation := P
  isMittagLeffler := hP

/-- Build a Mittag-Leffler presentation from a directed diagram, its
Mittag-Leffler property, and an isomorphism from its chosen colimit. -/
noncomputable def Presentation.ofIso
    {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    (F : I ⥤ ModuleCat.{max u v w} R) [HasColimit F]
    (hF : IsMittagLefflerDirectedSystem F)
    (c : colimit F ≅
      ModuleCat.of.{max u v w} R (ULift.{max u w} M)) : Presentation.{u, v, w} R M :=
  Presentation.ofColimit ((ColimitPresentation.colimit F).ofIso c) hF

end MittagLeffler

/-- An `R`-module is Mittag-Leffler if it is the colimit of a directed system satisfying
`IsMittagLefflerDirectedSystem`. -/
@[stacks 059F]
class MittagLeffler (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : Prop where
  /-- A concrete directed presentation witnessing the Mittag-Leffler property. -/
  exists_presentation :
    Nonempty (MittagLeffler.Presentation.{u, v, max u v} R M)

namespace MittagLeffler

/-- A concrete Mittag-Leffler presentation in the canonical joint universe of the ring and
module proves the intrinsic module property. -/
@[stacks 059F "presentation conversion"]
theorem Presentation.toMittagLeffler
    (P : Presentation.{u, v, max u v} R M) : MittagLeffler R M :=
  ⟨Nonempty.intro P⟩

end MittagLeffler

end

end Module
