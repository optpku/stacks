module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Subfunctor
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local representability in the big Zariski topology
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w

namespace AlgebraicGeometry.Scheme.LocalRepresentability

/-- A Zariski sheaf covered locally surjectively by representable open
subfunctors is representable. -/
@[stacks 01JJ]
theorem isRepresentable_of_locallySurjective_subfunctors
    (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
    {I : Type w} [Small.{u} I]
    (H : I → Subfunctor F.obj)
    (h_open : ∀ i, IsOpenImmersion.presheaf (H i).ι)
    (h_representable : ∀ i, (H i).toFunctor.IsRepresentable)
    (h_locallySurjective : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Limits.Sigma.desc (fun i ↦ (H i).ι))) :
    F.obj.IsRepresentable := sorry

/-- A Zariski sheaf covered by representable open subfunctors is
representable. -/
@[stacks 01JJ]
theorem isRepresentable_of_subfunctor_cover
    (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
    {I : Type w} [Small.{u} I]
    (H : I → Subfunctor F.obj)
    (h_open : ∀ i, IsOpenImmersion.presheaf (H i).ι)
    (h_representable : ∀ i, (H i).toFunctor.IsRepresentable)
    (h_cover : BigZariski.Subfunctor.IsZariskiCover H) :
    F.obj.IsRepresentable := sorry

/-- A Zariski sheaf covered by representable Zariski-open subfunctors is
representable. -/
@[stacks 01JJ]
theorem isRepresentable_of_zariskiOpen_subfunctor_cover
    (F : Sheaf Scheme.zariskiTopology.{u} (Type u))
    {I : Type w} [Small.{u} I]
    (H : I → Subfunctor F.obj)
    (h_open : ∀ i, BigZariski.Subfunctor.IsZariskiOpen (H i))
    (h_representable : ∀ i, (H i).toFunctor.IsRepresentable)
    (h_cover : BigZariski.Subfunctor.IsZariskiCover H) :
    F.obj.IsRepresentable := sorry

end AlgebraicGeometry.Scheme.LocalRepresentability
