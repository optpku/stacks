/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Split
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Pseudofunctor.CoGrothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- nLab distinguishes three layers: a cleavage is chosen lift data, a splitting is a cleavage
whose identity and composition laws hold strictly, and being represented by a Grothendieck
construction is a presentation property. The general `Cat`-valued layer already owns the last
property as `IsFibered.Split`; at the groupoid-valued layer the canonical reusable notion is
therefore its conjunction with `IsFibered.InGroupoids`, not a second copy of the same existential
presentation. The theorem below recovers the source's strict `Grpd`-valued model exactly. -/

/-- A split category fibred in groupoids is simultaneously a
split fibred category and a category fibred in groupoids.

This property-level owner composes the canonical general notions. The source presentation as a
strict isomorphism over `C` to some `(∫ᶜ F, p_F)` is exposed by
`IsFibered.Split.InGroupoids.iff_existsPresheafModel`. -/
@[stacks 04TL]
class IsFibered.Split.InGroupoids (p : S ⥤ C) : Prop extends
    Functor.IsFibered.Split p, Functor.IsFibered.InGroupoids p

namespace IsFibered.Split.InGroupoids

/-- The conjunction of split fibredness and fibredness in groupoids automatically supplies the
combined property. This is a coherent typeclass instance: it contains no choice beyond the two
already available property witnesses. -/
instance ofComponents (p : S ⥤ C)
    [Functor.IsFibered.Split p] [Functor.IsFibered.InGroupoids p] :
    Functor.IsFibered.Split.InGroupoids p where
  toSplit := inferInstance
  toInGroupoids := inferInstance

end IsFibered.Split.InGroupoids

/-- The canonical property-level definition agrees with the source presentation by a strict
groupoid-valued co-Grothendieck model, including heterogeneous total-category universes.

Proof strategy: from a model `F`, forget `Grpd` to `Cat` for splitness and transport
groupoidality across the strict based-category isomorphism. Conversely, unpack the strict
`Cat`-valued model supplied by `IsFibered.Split`; transport groupoidality from the fibers
of `p` to every value category, equip those categories with `Groupoid.ofIsGroupoid`, and package
the same object and map data as a functor to `Grpd`. Its forgotten co-Grothendieck projection is
definitionally the original model, so the existing based isomorphism finishes the comparison. -/
@[stacks 04TL "strict groupoid-valued model characterization"]
theorem IsFibered.Split.InGroupoids.iff_existsPresheafModel
    (p : S ⥤ C) :
    Functor.IsFibered.Split.InGroupoids p ↔
      ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
        Nonempty
          (BasedCategory.StrictIso (BasedCategory.ofFunctor p)
            (BasedCategory.ofFunctor (groupoidPresheafProjection F))) := sorry

end Functor

end CategoryTheory
