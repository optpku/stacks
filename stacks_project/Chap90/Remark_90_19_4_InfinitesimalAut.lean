/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Thin
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import stacks_project.Chap90.Definition_90_19_5_AutFunctor
public import stacks_project.Chap90.Remark_90_12_5_Slice
public import stacks_project.Chap90.Remark_90_19_3

/-!
# Infinitesimal automorphisms of a predeformation category

The residue fibre of a predeformation category is thin with unique isomorphisms,
so `infinitesimalAutomorphismsAt` is the full dual-number automorphism group.
The resulting group `infinitesimalAutomorphisms p` is independent of the chosen
residue-fibre object, and identifies with `infinitesimalAutomorphismsAt` of any
residue slice.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

namespace CategoryTheory.Functor

open Chosen

/-- The residue fibre of a predeformation category is a thin quiver. -/
instance instIsThin_residueFiber [IsPredeformationCategory p] :
    Quiver.IsThin (p.Fiber (residue Λ k)) :=
  fun x y ↦ (IsPredeformationCategory.unique_residueHom x y).2

/-- There is a unique morphism between any two objects of the residue fibre of a
predeformation category. -/
noncomputable instance instUniqueHom_residueFiber [IsPredeformationCategory p]
    (x0 y0 : p.Fiber (residue Λ k)) : Unique (x0 ⟶ y0) :=
  uniqueOfSubsingleton
    (Classical.choice (IsPredeformationCategory.unique_residueHom x0 y0).1)

/-- There is a unique isomorphism between any two objects of the residue fibre of a
predeformation category. -/
noncomputable instance instUniqueIso_residueFiber [IsPredeformationCategory p]
    (x0 y0 : p.Fiber (residue Λ k)) : Unique (x0 ≅ y0) :=
  uniqueOfSubsingleton (iso_of_both_ways (default : x0 ⟶ y0) (default : y0 ⟶ x0))

/-- The automorphism group of a residue-fibre object of a predeformation category is
trivial. -/
noncomputable instance instUniqueAut_residueFiber [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) : Unique (Aut x0) :=
  instUniqueIso_residueFiber p x0 x0

/-- In a predeformation category there is a unique morphism from any object to a
fixed residue-fibre object. -/
noncomputable instance instUniqueHom_toResidueFiberObj [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (y : F) :
    Unique (y ⟶ fiberInclusion.obj x0) where
  default :=
    Chosen.pushforwardHom p (toResidue (p.obj y)) (Fiber.ofObj p y) ≫
      fiberInclusion.map
        (default : Chosen.pushforwardObj p (toResidue (p.obj y)) (Fiber.ofObj p y) ⟶ x0)
  uniq := sorry

/-- Morphisms in `F` to a fixed residue-fibre object of a predeformation category are
equal. -/
theorem hom_eq_toResidueFiberObj [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {y : F} (f g : y ⟶ fiberInclusion.obj x0) :
    f = g := sorry

/-- In a predeformation category, `infinitesimalAutomorphismsAt` is the full dual-number
automorphism group. -/
theorem infinitesimalAutomorphismsAt_eq_top [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphismsAt p x0 x0' φ = ⊤ := sorry

/-- The canonical identification of infinitesimal automorphism groups along the unique
residue-fibre isomorphism. -/
noncomputable def infAutAtCanonicalIso [IsPredeformationCategory p]
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ] :
    infinitesimalAutomorphismsAt p x0 x0' φ ≃*
      infinitesimalAutomorphismsAt p y0 y0' ψ :=
  infAutAtIso_of_fiberIso p (default : x0 ≅ y0) φ ψ

/-- The underlying automorphism of `infAutAtCanonicalIso` is conjugation along the unique
vertical comparison of dual-number pushforwards. -/
theorem infAutAtCanonicalIso_apply [IsPredeformationCategory p]
    {x0 y0 : p.Fiber (residue Λ k)} {x0' y0' : p.Fiber (dualNumber Λ k)}
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    (ψ : fiberInclusion.obj y0 ⟶ fiberInclusion.obj y0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) ψ]
    (a : infinitesimalAutomorphismsAt p x0 x0' φ) :
    (infAutAtCanonicalIso p φ ψ a).val =
      (fiberIso_of_fiberIso p (default : x0 ≅ y0) φ ψ).conjAut a.val := sorry

/-- A chosen object of the residue fibre of a predeformation category. -/
noncomputable def chosenResidueFiberObj [IsPredeformationCategory p] :
    p.Fiber (residue Λ k) :=
  Classical.choice IsPredeformationCategory.nonempty_residueFiber

/-- Any residue-fibre object is isomorphic to `chosenResidueFiberObj`. -/
theorem chosenResidueFiberObj_uniqueIso [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) :
    Nonempty (chosenResidueFiberObj p ≅ x0) := sorry

/-- The group of infinitesimal automorphisms of a predeformation category, as automorphisms
of the selected dual-number pushforward of a chosen residue-fibre object. -/
noncomputable abbrev infinitesimalAutomorphisms [IsPredeformationCategory p] : Type w :=
  Aut (Chosen.pushforwardObj p (residueToDualNumber Λ k) (chosenResidueFiberObj p))

/-- `infinitesimalAutomorphisms p` is the automorphism group of the selected dual-number
pushforward of `chosenResidueFiberObj p`. -/
theorem infinitesimalAutomorphisms_def [IsPredeformationCategory p] :
    infinitesimalAutomorphisms p =
      Aut (Chosen.pushforwardObj p (residueToDualNumber Λ k)
        (chosenResidueFiberObj p)) := sorry

/-- The selected dual-number pushforward of a residue-fibre object, as a morphism of
fibre-inclusion objects. -/
noncomputable def chosenDualNumberHom [p.op.IsFibered] (x0 : p.Fiber (residue Λ k)) :
    fiberInclusion.obj x0 ⟶
      fiberInclusion.obj (Chosen.pushforwardObj p (residueToDualNumber Λ k) x0) :=
  Chosen.pushforwardHom p (residueToDualNumber Λ k) x0

/-- The selected dual-number pushforward of a residue-fibre object is strongly cocartesian. -/
instance instIsStronglyCocartesian_chosenDualNumberHom [p.op.IsFibered]
    (x0 : p.Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToDualNumber Λ k) (chosenDualNumberHom p x0) :=
  Chosen.pushforwardHom.isStronglyCocartesian p (residueToDualNumber Λ k) x0

/-- Choice-independence of `infinitesimalAutomorphisms`: conjugation along the unique
comparison of selected dual-number pushforwards. -/
noncomputable def infinitesimalAutomorphismsMulEquiv [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) :
    infinitesimalAutomorphisms p ≃*
      Aut (Chosen.pushforwardObj p (residueToDualNumber Λ k) x0) :=
  (fiberIso_of_fiberIso p (default : chosenResidueFiberObj p ≅ x0)
      (chosenDualNumberHom p (chosenResidueFiberObj p))
      (chosenDualNumberHom p x0)).conjAut

/-- `infinitesimalAutomorphismsMulEquiv` acts by conjugation along the unique comparison of
selected dual-number pushforwards. -/
theorem infinitesimalAutomorphismsMulEquiv_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (α : infinitesimalAutomorphisms p) :
    infinitesimalAutomorphismsMulEquiv p x0 α =
      (fiberIso_of_fiberIso p (default : chosenResidueFiberObj p ≅ x0)
          (chosenDualNumberHom p (chosenResidueFiberObj p))
          (chosenDualNumberHom p x0)).conjAut α := sorry

/-- Well-definedness of `infinitesimalAutomorphisms`: it is canonically identified with
`infinitesimalAutomorphismsAt` at any residue-fibre object and dual-number pushforward. -/
noncomputable def infinitesimalAutomorphismsEquivAt [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphisms p ≃* infinitesimalAutomorphismsAt p x0 x0' φ :=
  let e := fiberIso_of_fiberIso p (default : chosenResidueFiberObj p ≅ x0)
    (chosenDualNumberHom p (chosenResidueFiberObj p)) φ
  { toFun α := ⟨e.conjAut α, sorry⟩
    invFun β := e.symm.conjAut β.val
    left_inv := sorry
    right_inv := sorry
    map_mul' := sorry }

/-- The underlying automorphism of `infinitesimalAutomorphismsEquivAt` is conjugation along
the unique residue-fibre isomorphism and the unique dual-number comparison. -/
theorem infinitesimalAutomorphismsEquivAt_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphisms p) :
    (infinitesimalAutomorphismsEquivAt p x0 x0' φ α).val =
      (fiberIso_of_fiberIso p (default : chosenResidueFiberObj p ≅ x0)
          (chosenDualNumberHom p (chosenResidueFiberObj p)) φ).conjAut α := sorry

/-- The fibre object of `p` obtained by forgetting the over-category structure of a fibre
object of the residue slice. -/
def sliceFiberObj [IsFibered.InGroupoids p.op] (x0 : p.Fiber (residue Λ k))
    {U : ArtinianLocalAlgCat Λ k} (y : (sliceAt p x0).Fiber U) : p.Fiber U :=
  ⟨y.1.left, y.2⟩

/-- A chosen residue-fibre object of the residue slice `sliceAt p x0`. -/
noncomputable def chosenSliceResidueFiberObj [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) :
    (sliceAt p x0).Fiber (residue Λ k) :=
  chosenResidueFiberObj (sliceAt p x0)

/-- `chosenSliceResidueFiberObj` is the chosen residue-fibre object of `sliceAt p x0`. -/
theorem chosenSliceResidueFiberObj_eq [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) :
    chosenSliceResidueFiberObj p x0 = chosenResidueFiberObj (sliceAt p x0) := sorry

/-- Automorphisms of a slice-fibre object are automorphisms of the underlying fibre object
of `p`, via `Over.forget`. This uses uniqueness of morphisms to the residue-fibre object,
so every fibre automorphism preserves the over-category structure map. -/
noncomputable def sliceFiberAutMulEquiv [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) {U : ArtinianLocalAlgCat Λ k}
    (y : (sliceAt p x0).Fiber U) :
    Aut y ≃* Aut (sliceFiberObj p x0 y) where
  toFun α :=
    Fiber.isoMk ((Over.forget (fiberInclusion.obj x0)).mapIso (fiberInclusion.mapIso α)) sorry
  invFun β :=
    Fiber.isoMk
      (Over.isoMk (fiberInclusion.mapIso β)
        (hom_eq_toResidueFiberObj p x0 ((fiberInclusion.mapIso β).hom ≫ y.1.hom) y.1.hom))
      sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The image under `Over.forget` of the selected dual-number pushforward in a residue slice. -/
noncomputable def sliceChosenDualNumberHom [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (y0 : (sliceAt p x0).Fiber (residue Λ k)) :
    fiberInclusion.obj (sliceFiberObj p x0 y0) ⟶
      fiberInclusion.obj
        (sliceFiberObj p x0
          (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k) y0)) :=
  (Over.forget (fiberInclusion.obj x0)).map
    (Chosen.pushforwardHom (sliceAt p x0) (residueToDualNumber Λ k) y0)

/-- The selected dual-number pushforward of a residue-fibre object of the residue slice
forgets to a strongly cocartesian lift in `F`. -/
instance instIsStronglyCocartesian_slicePushforward_forget [IsFibered.InGroupoids p.op]
    (x0 : p.Fiber (residue Λ k)) (y0 : (sliceAt p x0).Fiber (residue Λ k)) :
    p.IsStronglyCocartesian (residueToDualNumber Λ k)
      (sliceChosenDualNumberHom p x0 y0) := sorry

/-- The identification `infinitesimalAutomorphisms (sliceAt p x0) ≃*
infinitesimalAutomorphismsAt p x0 x0' φ`, with underlying map the forgetful automorphism
map of `Over.forget`. -/
noncomputable def infinitesimalAutomorphisms_sliceAt [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ] :
    infinitesimalAutomorphisms (sliceAt p x0) ≃*
      infinitesimalAutomorphismsAt p x0 x0' φ :=
  let y0 := chosenSliceResidueFiberObj p x0
  let e :=
    fiberIso_of_fiberIso p (default : sliceFiberObj p x0 y0 ≅ x0)
      (sliceChosenDualNumberHom p x0 y0) φ
  { toFun α :=
      ⟨e.conjAut
          (sliceFiberAutMulEquiv p x0
            (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k) y0) α),
        sorry⟩
    invFun β :=
      (sliceFiberAutMulEquiv p x0
          (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k) y0)).symm
        (e.symm.conjAut β.val)
    left_inv := sorry
    right_inv := sorry
    map_mul' := sorry }

/-- The underlying automorphism of `infinitesimalAutomorphisms_sliceAt` is conjugation of
the forgetful `Over.forget` map on automorphisms. -/
theorem infinitesimalAutomorphisms_sliceAt_apply [IsPredeformationCategory p]
    (x0 : p.Fiber (residue Λ k)) (x0' : p.Fiber (dualNumber Λ k))
    (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
    [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]
    (α : infinitesimalAutomorphisms (sliceAt p x0)) :
    (infinitesimalAutomorphisms_sliceAt p x0 x0' φ α).val =
      (fiberIso_of_fiberIso p
          (default : sliceFiberObj p x0 (chosenSliceResidueFiberObj p x0) ≅ x0)
          (sliceChosenDualNumberHom p x0 (chosenSliceResidueFiberObj p x0)) φ).conjAut
        (sliceFiberAutMulEquiv p x0
          (Chosen.pushforwardObj (sliceAt p x0) (residueToDualNumber Λ k)
            (chosenSliceResidueFiberObj p x0)) α) := sorry

end CategoryTheory.Functor
