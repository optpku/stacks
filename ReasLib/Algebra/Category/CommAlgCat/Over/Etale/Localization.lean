module

public import ReasLib.Algebra.Category.CommAlgCat.Over.Target.Localization
public import ReasLib.Algebra.Category.CommAlgCat.Over.Etale
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

/-!
# Localized pointed etale algebras

The target-kernel localization maps, their relative algebra structures, and
their ring-level functoriality are owned by `CommAlgCat.Over.Target.Localization`.
This leaf adds precisely the facts that use the etaleness of an object and the
resulting categorical diagram.

@stack 04GV
-/

universe u v

namespace CommAlgCat.Over.Etale

namespace Localization

variable {R : Type u} {T : Type v} [CommRing R] [CommRing T] [IsDomain T] [Algebra R T]
variable {p : Ideal R} [p.IsPrime]

/-- Localizing a pointed etale algebra at its target kernel is etale over the
localization at the contracted base prime.  The map-level formulation avoids
exposing a temporary relative-algebra instance in the public statement. -/
@[stacks 04GV "etaleness of a pointed etale prime localization"]
theorem etale
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CommAlgCat.Over.Etale.category R T) :
    RingHom.Etale (CommAlgCat.Over.Target.Localization.map hbase A.obj) := sorry

/-- The canonical prime-localization map of a pointed etale algebra is
ind-etale over the base localization. -/
@[stacks 04GV "ind-etaleness of a pointed etale prime localization"]
theorem indEtale
    (hbase : RingHom.ker (algebraMap R T) = p)
    (A : CommAlgCat.Over.Etale.category R T) :
    RingHom.IndEtale (CommAlgCat.Over.Target.Localization.map hbase A.obj) := sorry

/-! ### Etale restriction -/

/-- The localized pointed etale diagram is the restriction of the neutral
target-kernel localization functor to etale over-objects. -/
@[stacks 04GV "localized pointed etale diagram"]
noncomputable def diagram
    (hbase : RingHom.ker (algebraMap R T) = p) :
    CommAlgCat.Over.Etale.category R T ⥤
      CommAlgCat (_root_.Localization.AtPrime p) :=
  (property R T).ι ⋙ CommAlgCat.Over.Target.Localization.functor hbase

end Localization

end CommAlgCat.Over.Etale
