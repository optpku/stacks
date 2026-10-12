/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Iso.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Morphism.Iso.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse Naturality for Isomorphisms of Telescope Presentations

The inverse-facing compatibility equations for a presentation isomorphism.  These equations use
the inverse natural transformation on the sequential diagrams, so downstream arguments can move
from the target presentation to the source without manually expanding `Presentation.Iso.symm`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.Presentation.Iso

open Limits.Sequential

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The inverse presentation isomorphism transports the target coproduct cocone map to the
source presentation. -/
@[reassoc, stacks 0CRH]
theorem toCocone_naturality_inv {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Q.toCocone ≫ Φ.iso.inv =
      ColimitCocone.Discrete.map Q.coproduct P.coproduct e.inv.app ≫ P.toCocone := sorry

/-- The inverse presentation isomorphism transports the target connecting map to the source
after the shifted inverse coproduct map. -/
@[reassoc, stacks 0CRH]
theorem connecting_naturality_inv {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) :
    Q.connecting ≫
        (ColimitCocone.Discrete.map Q.coproduct P.coproduct e.inv.app)⟦(1 : ℤ)⟧' =
      Φ.iso.inv ≫ P.connecting := sorry

/-- The inverse presentation isomorphism transports every target stage map to the corresponding
source stage map. -/
@[reassoc, stacks 0CRH]
theorem ι_naturality_inv {S T : ℕ ⥤ D} {e : S ≅ T} {X Y : D}
    {P : HomotopyColimit.Presentation S X} {Q : HomotopyColimit.Presentation T Y}
    (Φ : HomotopyColimit.Presentation.Iso e P Q) (n : ℕ) :
    Q.ι n ≫ Φ.iso.inv = e.inv.app n ≫ P.ι n := sorry

end CategoryTheory.HomotopyColimit.Presentation.Iso
