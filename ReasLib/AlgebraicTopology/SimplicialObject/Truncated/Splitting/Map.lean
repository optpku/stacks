module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial images of truncated splittings

This leaf sends chosen truncated splittings through functors preserving finite coproducts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe v u v₂ u₂

namespace CategoryTheory.SimplicialObject.Truncated.Splitting

variable {C : Type u} [Category.{v} C]
variable {n : ℕ} {X : SimplicialObject.Truncated C n} (s : Splitting X)

namespace map

/-- Apply a functor to the apex and injections of a truncated splitting cofan. -/
@[stacks 017P "functorial image of a truncated splitting cofan"]
def cofan {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Cofan (fun A : IndexSet Δ ↦ F.obj (summand s.N Δ A)) :=
  Cofan.mk (F.obj (X.obj Δ)) fun A ↦ F.map ((s.cofan Δ).inj A)

/-- Applying a finite-coproduct-preserving functor to a splitting cofan preserves its concrete
colimit structure. -/
@[stacks 017P "colimit structure on a functorial splitting cofan"]
def cofanIsColimit {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    IsColimit (cofan s F Δ) :=
  isColimitCofanMkObjOfIsColimit F (summand s.N Δ)
    (fun A ↦ (s.cofan Δ).inj A) (s.isColimit Δ)

/-- Compatibility of the cofan injections in the two presentations of a functorial splitting
cofan. -/
@[stacks 017P "cofan compatibility for a functorial truncated splitting"]
theorem cofan_inj {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ) :
    (cofan s F Δ).inj A =
      (cofan' (fun m ↦ F.obj (s.N m)) (X ⋙ F)
        (fun m ↦ F.map (s.ι m)) Δ).inj A := sorry

section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-- Compatibility of cofan injections in the fac form required by `Cofan.ext`. -/
@[stacks 017P "faceted cofan compatibility for a functorial truncated splitting"]
private theorem cofan_inj_fac {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ) :
    (cofan s F Δ).inj A ≫ 𝟙 (F.obj (X.obj Δ)) =
      (cofan' (fun m ↦ F.obj (s.N m)) (X ⋙ F)
        (fun m ↦ F.map (s.ι m)) Δ).inj A := sorry

/-- The canonical cofan isomorphism used to transport a splitting through a functor. -/
@[stacks 017P "cofan isomorphism for a functorial truncated splitting"]
def cofanIso {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    cofan s F Δ ≅
      cofan' (fun m ↦ F.obj (s.N m)) (X ⋙ F)
        (fun m ↦ F.map (s.ι m)) Δ :=
  Cofan.ext (Iso.refl _) (cofan_inj_fac s F (Δ := Δ))

end

/-- A functor preserving finite coproducts sends the cofan of a truncated splitting to a
concretely colimiting cofan. -/
@[stacks 017P "functorial colimit transport for a truncated splitting"]
def isColimit {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    IsColimit
      (cofan' (fun m ↦ F.obj (s.N m)) (X ⋙ F)
        (fun m ↦ F.map (s.ι m)) Δ) :=
  IsColimit.ofIsoColimit (cofanIsColimit s F Δ) (cofanIso s F Δ)

end map

/-- Apply a finite-coproduct-preserving functor to a chosen truncated splitting. -/
@[stacks 017P "functorial image of a truncated splitting"]
def map {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] : Splitting (X ⋙ F) where
  N m := F.obj (s.N m)
  ι m := F.map (s.ι m)
  isColimit' := map.isColimit s F

/-- Formula for the summand objects of the functorial image of a splitting. -/
@[simp, stacks 017P "summands of the functorial image of a truncated splitting"]
theorem map_N {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] (m : Fin (n + 1)) :
    (s.map F).N m = F.obj (s.N m) := sorry

/-- Formula for the distinguished maps of the functorial image of a splitting. -/
@[simp, stacks 017P "summand maps of the functorial image of a truncated splitting"]
theorem map_ι {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    [PreservesFiniteCoproducts F] (m : Fin (n + 1)) :
    (s.map F).ι m = F.map (s.ι m) := sorry

end CategoryTheory.SimplicialObject.Truncated.Splitting
