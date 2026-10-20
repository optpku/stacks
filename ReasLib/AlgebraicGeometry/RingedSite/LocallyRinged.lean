module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.RingedSite.Topos
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally ringed commutative ringed-site presentations

This leaf bridges the sheaf-level locally ringed predicate to bundled ringed-site equivalences.
The intrinsic sheaf criterion remains in the algebraic sheaf hierarchy; only the bundling bridge
lives here.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite.Hom

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [JC.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [JD.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify JC (Type (max u v))]
variable [JC.HasSheafCompose (forget CommRingCat.{max u v})]
variable [HasWeakSheafify JD (Type (max u v))]
variable [JD.HasSheafCompose (forget CommRingCat.{max u v})]
variable {𝒪C : Sheaf JC CommRingCat.{max u v}}
variable {𝒪D : Sheaf JD CommRingCat.{max u v}}

/-- Lemma 18.40.5 (04H7), bundled form: a ringed equivalence preserves and reflects locally
ringedness of the commutative structure sheaves. -/
@[stacks 04H7 "ringed equivalence"]
theorem isLocallyRinged_iff_of_equivalence
    (f : RingedSite.Hom (RingedSite.ofCommRingSheaf JC 𝒪C)
      (RingedSite.ofCommRingSheaf JD 𝒪D))
    [f.IsRingedEquivalence] :
    𝒪C.IsLocallyRinged ↔ 𝒪D.IsLocallyRinged := sorry

end RingedSite.Hom
