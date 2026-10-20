module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace
public import ReasLib.CategoryTheory.DerivedCategory.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived gluing along a well-ordered open cover

The indexed owner deliberately does not quotient by the range of the open family: the same open
may occur at several indices, carrying different specified comparison data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped DerivedExt

noncomputable section

universe u v

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.WellOrdered

open OpenSubspace.Restriction

variable {X : RingedSpace.{u}} {E : Type v}
  [LinearOrder E] [SuccOrder E] [WellFoundedLT E]

/-- Coherent local derived modules indexed by an increasing well-ordered family of opens. -/
@[stacks 0D6B "derived gluing system on a well-ordered open family"]
structure System (X : RingedSpace.{u}) (W : E → Opens X.carrier) where
  /-- The indexed open family is increasing. -/
  monotone : Monotone W
  /-- The local derived module at an index. -/
  obj (α : E) : moduleDerivedOnOpen X (W α)
  /-- Restriction from a later index to an earlier index. -/
  ρ {β α : E} (hβα : β < α) :
    (derivedBetween X (monotone hβα.le)).obj (obj α) ≅ obj β
  /-- Indexed restriction isomorphisms compose. -/
  ρ_comp {γ β α : E} (hγβ : γ < β) (hβα : β < α) :
    ((derivedBetweenCompIso X (monotone hγβ.le) (monotone hβα.le)).app (obj α)) ≪≫
        ρ (lt_trans hγβ hβα) =
      (derivedBetween X (monotone hγβ.le)).mapIso (ρ hβα) ≪≫ ρ hγβ

namespace System

variable {W : E → Opens X.carrier}

/-- Negative self-Ext groups of every indexed local object vanish. -/
@[stacks 0D6B "negative self-Ext vanishing on a well-ordered gluing system"]
abbrev NegativeSelfExtVanishing (S : System X W) : Prop :=
  ∀ α (i : ℤ), i < 0 → IsZero (AddCommGrpCat.of (Ext⁽i⁾(S.obj α, S.obj α)))

/-- Indexed restriction isomorphisms from an ambient object to a well-ordered gluing system. -/
@[stacks 0D6B "local identifications for a well-ordered gluing realization"]
abbrev LocalIso (S : System X W) (K : ModuleDerived X) :=
  ∀ α : E, (moduleRestrictionToOpenDerived X (W α)).obj K ≅ S.obj α

/-- Indexed local identifications respect all transition isomorphisms. -/
@[stacks 0D6B "compatibility of a well-ordered gluing realization"]
def IsRealization (S : System X W) (K : ModuleDerived X) (e : S.LocalIso K) : Prop :=
  ∀ {β α : E} (hβα : β < α),
    CommSq ((derivedCompIso X (S.monotone hβα.le)).app K).inv (e β).hom
      ((derivedBetween X (S.monotone hβα.le)).map (e α).hom) (S.ρ hβα).inv

/-- A bundled realization of a well-ordered gluing system. -/
@[stacks 0D6B "realization of a well-ordered derived gluing system"]
structure Realization (S : System X W) (K : ModuleDerived X) where
  /-- The indexed local identifications. -/
  iso : S.LocalIso K
  /-- Compatibility with every transition isomorphism. -/
  compatible : S.IsRealization K iso

/-- A well-ordered gluing system admits an ambient realization. -/
@[stacks 0D6B "existence of a well-ordered gluing realization"]
abbrev HasRealization (S : System X W) : Prop :=
  ∃ K : ModuleDerived X, Nonempty (S.Realization K)

/-- Source-facing existential characterization of a well-ordered realization. -/
@[stacks 0D6B "existential characterization of a well-ordered gluing realization"]
theorem hasRealization_iff_exists (S : System X W) :
    S.HasRealization ↔
      ∃ (K : ModuleDerived X) (e : S.LocalIso K), S.IsRealization K e := sorry

/-- Lemma 20.45.7: a continuous well-ordered open cover with negative local self-Ext vanishing
admits an ambient derived realization. -/
@[stacks 0D6B "derived gluing along a continuous well-ordered open cover"]
theorem existsRealization (S : System X W) (hcover : iSup W = ⊤)
    (hlimit : ∀ ⦃α : E⦄, Order.IsSuccPrelimit α → W α = ⨆ β : Set.Iio α, W β.1)
    (hneg : S.NegativeSelfExtVanishing) : S.HasRealization := sorry

/-- One compatibility square of a bundled well-ordered realization. -/
@[stacks 0D6B "compatibility square of a well-ordered gluing realization"]
theorem Realization.commSq {S : System X W} {K : ModuleDerived X}
    (R : S.Realization K) {β α : E} (hβα : β < α) :
    CommSq ((derivedCompIso X (S.monotone hβα.le)).app K).inv (R.iso β).hom
      ((derivedBetween X (S.monotone hβα.le)).map (R.iso α).hom) (S.ρ hβα).inv := sorry

end System

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.WellOrdered

end
