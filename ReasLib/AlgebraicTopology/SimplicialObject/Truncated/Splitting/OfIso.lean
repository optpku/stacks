module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transporting truncated splittings along isomorphisms

This leaf transports chosen splitting data along an isomorphism of truncated simplicial objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated.Splitting

variable {C : Type u} [Category.{v} C]
variable {n : ℕ} {X : SimplicialObject.Truncated C n} (s : Splitting X)

namespace ofIso

/-- Compatibility of the cofan injections when a splitting is transported along an
isomorphism. -/
@[stacks 017P "cofan compatibility for an isomorphism of truncated simplicial objects"]
theorem cofan_inj {Y : SimplicialObject.Truncated C n} (e : X ≅ Y)
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ) :
    (s.cofan Δ).inj A ≫ e.hom.app Δ =
      (cofan' s.N Y (fun m ↦ s.ι m ≫ e.hom.app (op ⦋m⦌ₙ)) Δ).inj A := sorry

/-- The cofan isomorphism induced by transporting a splitting along an isomorphism. -/
@[stacks 017P "cofan isomorphism for a transported truncated splitting"]
def cofanIso {Y : SimplicialObject.Truncated C n} (e : X ≅ Y)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    s.cofan Δ ≅
      cofan' s.N Y (fun m ↦ s.ι m ≫ e.hom.app (op ⦋m⦌ₙ)) Δ :=
  Cofan.ext (e.app Δ) (cofan_inj s e (Δ := Δ))

/-- The concrete colimit structure on a cofan transported along an isomorphism. -/
@[stacks 017P "colimit transport for a truncated splitting"]
def isColimit {Y : SimplicialObject.Truncated C n} (e : X ≅ Y)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    IsColimit
      (cofan' s.N Y (fun m ↦ s.ι m ≫ e.hom.app (op ⦋m⦌ₙ)) Δ) :=
  IsColimit.ofIsoColimit (s.isColimit Δ) (cofanIso s e Δ)

end ofIso

/-- Transport a chosen truncated splitting along an isomorphism of truncated simplicial
objects. -/
@[stacks 017P "transport of a truncated splitting along an isomorphism"]
def ofIso {Y : SimplicialObject.Truncated C n} (e : X ≅ Y) : Splitting Y where
  N := s.N
  ι m := s.ι m ≫ e.hom.app (op ⦋m⦌ₙ)
  isColimit' := ofIso.isColimit s e

/-- Transporting a splitting along an isomorphism preserves its chosen summand objects. -/
@[simp, stacks 017P "summands after transporting a truncated splitting"]
theorem ofIso_N {Y : SimplicialObject.Truncated C n} (e : X ≅ Y)
    (m : Fin (n + 1)) :
    (s.ofIso e).N m = s.N m := sorry

/-- Formula for the distinguished maps of a splitting transported along an isomorphism. -/
@[simp, stacks 017P "summand maps after transporting a truncated splitting"]
theorem ofIso_ι {Y : SimplicialObject.Truncated C n} (e : X ≅ Y)
    (m : Fin (n + 1)) :
    (s.ofIso e).ι m = s.ι m ≫ e.hom.app (op ⦋m⦌ₙ) := sorry

end CategoryTheory.SimplicialObject.Truncated.Splitting
